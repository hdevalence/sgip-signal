//! Unofficial Rust bindings to the [SGIP Signal API][sgipsignal],
//! which provides access to real-time and forecasted marginal Greenhouse Gas
//! (GHG) emissions data for participants in California's Self Generation
//! Incentive Program (SGIP).
//!
//! More information is available on the [SGIP Signal website][sgipsignal]:
//!
//! > Further details about SGIP itself can be found on the
//! > [SGIP website][sgipwebsite]. The SGIP
//! > program is implementing new GHG requirements, which are explained in the
//! > [SGIP Handbook][sgiphandbook]. This website provides data which will
//! > assist energy storage developers, operators, and others in implementing
//! > those rules.
//!
//! The API reports GHG emissions data in the form of Marginal Operating
//! Emissions Rates (MOERs), represented in this crate by the [`Moer`] type.
//! Forecasted MOERs are represented by the [`Forecast`] type, whose
//! [`Forecast::at`] method allows querying forecasted data. API calls are
//! performed using the [`SgipSignal`] type, which represents an authenticated
//! session with the API and automatically handles credential lifetimes and
//! periodic reauthentication.
//!
//! This crate currently supports the following subset of the API:
//!
//! - ☐ user registration (use a one-off `curl` command for now);
//! - ☑ user authentication and session management, using the [`SgipSignal`] type;
//! - ☑ current MOER data, using [`SgipSignal::moer`];
//! - ☑ historical MOER data, using [`SgipSignal::historic_moers`];
//! - ☑ current short-term (72-hour) MOER forecasts, using [`SgipSignal::forecast`];
//! - ☑ historical short-term (72-hour) MOER forecasts, using [`SgipSignal::historic_forecasts`];
//! - ☐ current long-term (1-month and 1-year) MOER forecasts;
//! - ☐ historical long-term (1-month and 1-year) MOER forecasts;
//! - ☐ rate limiting and backpressure;
//!
//! This is an unofficial set of bindings, with no guarantees about maintenance
//! or functional correctness.
//!
//! [sgipsignal]: https://sgipsignal.com/
//! [sgipwebsite]: https://www.selfgenca.com/
//! [sgiphandbook]: https://www.selfgenca.com/home/resources/

use std::{collections::BTreeMap, str::FromStr};

use anyhow::{anyhow, Error};
use chrono::{DateTime, Duration, Utc};
use serde::{Deserialize, Serialize};

/// A Marginal Operating Emissions Rate (MOER).
#[derive(Deserialize, Debug, Clone)]
pub struct Moer {
    /// The grid region for the rate.
    #[serde(rename = "ba")]
    pub region: GridRegion,
    /// The emissions rate itself, in kg CO2 / kWh.
    #[serde(rename = "moer", deserialize_with = "serde_help::de_f64_from_str")]
    pub rate: f64,
    /// The start time for the rate.
    #[serde(rename = "point_time")]
    pub start: DateTime<Utc>,
    /// The duration for rate.
    #[serde(rename = "freq", with = "serde_help::SecondsDuration")]
    pub duration: Duration,
}

/// A forecast of future MOERs.
///
/// To get the [`Moer`] this forecast predicts at a given time, use
/// [`Forecast::at`].
#[derive(Deserialize, Debug, Clone)]
#[serde(try_from = "serde_help::ForecastRaw")]
pub struct Forecast {
    /// The grid region for the forecast.
    pub region: GridRegion,
    /// The time when the forecast was generated.
    pub generated_at: DateTime<Utc>,
    /// The forecast itself, mapping the start time of each interval to the emissions rate, in kg CO2 / kWh.
    pub data: BTreeMap<DateTime<Utc>, f64>,
}

impl Forecast {
    /// Return the forecasted [`Moer`] for the given `time`, or `None` if the
    /// `time` is not included in the forecast.
    ///
    /// Note: because the forecast data returned by the SGIP Signal API does not
    /// include explicit end-times, this method treats the start of the next time
    /// interval as the end of the previous one, and therefore treats the start
    /// of the last time interval as the end of the forecast range.
    pub fn at(&self, time: DateTime<Utc>) -> Option<Moer> {
        use std::ops::Bound::{Excluded, Included, Unbounded};
        let before = self.data.range((Unbounded, Included(time))).rev().next();
        let after = self.data.range((Excluded(time), Unbounded)).next();

        match (before, after) {
            (Some((start, rate)), Some((end, _next_rate))) => Some(Moer {
                region: self.region,
                rate: *rate,
                start: *start,
                duration: *end - *start,
            }),
            _ => None,
        }
    }
}

/// An authenticated session with the SGIP Signal API.
///
/// After [registering an account][register], create a new session using
/// [`SgipSignal::login`]. The SGIP Signal API performs authentication using
/// bearer tokens valid for 30 minutes; the `SgipSignal` type automatically
/// refreshes the bearer tokens as required.
///
/// [register]:
/// https://jsapi.apiary.io/apis/sgip1/reference/authentication/register/create-new-user-account.html
#[derive(Debug)]
pub struct SgipSignal {
    username: String,
    password: String,
    client: reqwest::Client,
    token: Option<String>,
    issued_at: Option<DateTime<Utc>>,
}

impl SgipSignal {
    /// Log in to the SGIP Signal API, producing a new session token on success.
    #[tracing::instrument(skip(password))]
    pub async fn login(username: &str, password: &str) -> Result<Self, Error> {
        let client = reqwest::Client::new();

        let mut token = Self {
            client,
            username: username.to_owned(),
            password: password.to_owned(),
            token: None,
            issued_at: None,
        };

        token.renew().await?;

        Ok(token)
    }

    fn still_valid(&self) -> bool {
        if let Some(issued_at) = self.issued_at {
            // Tokens are valid for 30 minutes; use a 29-minute expiry to avoid
            // expiration during an API call.
            Utc::now() < issued_at + Duration::minutes(29)
        } else {
            false
        }
    }

    #[tracing::instrument(skip(self))]
    async fn renew(&mut self) -> Result<(), Error> {
        if self.still_valid() {
            tracing::trace!("token is still valid");
            return Ok(());
        }

        tracing::debug!("renewing expiring token");
        let rsp = self
            .client
            .get("https://sgipsignal.com/login/")
            .basic_auth(&self.username, Some(&self.password))
            .send()
            .await?
            .text()
            .await?;

        tracing::trace!(?rsp);

        self.token = Some(
            serde_json::from_str::<serde_json::Value>(&rsp)?["token"]
                .as_str()
                .map(String::from)
                .ok_or_else(|| anyhow::anyhow!("Login succeded but did not give a token"))?,
        );
        self.issued_at = Some(Utc::now());

        Ok(())
    }

    /// Fetch the latest MOER for the specified grid
    /// region.
    ///
    /// Per the [API description][api], this returns the *latest* MOER data,
    /// which may not be the *current* data:
    ///
    /// > Note that MOERs are usually available two to three minutes before the
    /// > timestamp for which they are valid. For example, the MOER valid from
    /// > 12:00 to 12:05 will typically become available through the API around
    /// > 11:58 and will be published no later than 12:00. The availability of the
    /// > next MOER datapoint is dependent on when CAISO market data becomes
    /// > available and as such is somewhat variable.
    ///
    /// [api]: https://jsapi.apiary.io/apis/sgip1/reference/grid-information/marginal-emissions/sgipmoer.html
    #[tracing::instrument(skip(self))]
    pub async fn moer(&mut self, region: GridRegion) -> Result<Moer, Error> {
        self.renew().await?;

        let req = self
            .client
            .get("https://sgipsignal.com/sgipmoer/")
            .bearer_auth(self.token.as_ref().expect("recently renewed token"))
            .query(&[("ba", region.to_string())]);
        tracing::debug!(?req);

        let rsp = req.send().await?.text().await?;
        tracing::trace!(?rsp);
        let moer = serde_json::from_str(&rsp)?;

        Ok(moer)
    }

    /// Fetch historic MOERs for the specified grid region.
    ///
    /// If the `end` time is `None`, the query requests data from the `start` time to the present.
    ///
    /// The [API description][api] notes that
    ///
    /// > Historical queries are limited to a maximum time span of 31 days.
    ///
    /// [api]: https://jsapi.apiary.io/apis/sgip1/reference/grid-information/marginal-emissions/sgipmoer.html
    #[tracing::instrument(skip(self))]
    pub async fn historic_moers(
        &mut self,
        region: GridRegion,
        start: DateTime<Utc>,
        end: Option<DateTime<Utc>>,
    ) -> Result<Vec<Moer>, Error> {
        self.renew().await?;

        let req = self
            .client
            .get("https://sgipsignal.com/sgipmoer/")
            .bearer_auth(self.token.as_ref().expect("recently renewed token"))
            .query(&[("ba", region.to_string())]);

        let req = match end {
            None => req.query(&[("starttime", start.to_rfc3339())]),
            Some(end) => req.query(&[
                ("starttime", start.to_rfc3339()),
                ("endtime", end.to_rfc3339()),
            ]),
        };

        tracing::debug!(?req);
        let rsp = req.send().await?.text().await?;
        tracing::trace!(?rsp);
        let moers = serde_json::from_str(&rsp)?;

        Ok(moers)
    }

    /// Fetch the latest forecast for future MOERs
    /// in the specified grid region.
    #[tracing::instrument(skip(self))]
    pub async fn forecast(&mut self, region: GridRegion) -> Result<Forecast, Error> {
        self.renew().await?;

        let req = self
            .client
            .get("https://sgipsignal.com/sgipforecast/")
            .bearer_auth(self.token.as_ref().expect("recently renewed token"))
            .query(&[("ba", region.to_string())]);

        tracing::debug!(?req);
        let rsp = req.send().await?.text().await?;
        tracing::trace!(?rsp);
        let forecast = serde_json::from_str(&rsp)?;

        Ok(forecast)
    }

    /// Fetch the historic forecasts for future Marginal Operating Emissions
    /// Rates in the specified grid region.
    ///
    /// Note that the `start` and `end` parameters select the time range when the
    /// forecasts were **generated**, not the time range *predicted* by those
    /// forecasts, as described in the [API description][api]:
    ///
    /// > Every five minutes, WattTime generates a new forecast which is 72 hours
    /// > in duration. So, if you make a request to the forecast endpoint with
    /// > `starttime` of Jan 1, 1:00 and `endtime` Jan 1, 1:05, you will receive the
    /// > 72-hour forecast generated at 1:00, and the 72-hour forecast generated at
    /// > 1:05 on January 1.
    ///
    /// The following limits apply to historical queries:
    ///
    /// > Historical forecast queries are limited to a maximum time span of 1 day
    /// > - so if you want to query more data than that, please break up your
    /// > request into multiple queries. A year of historical forecast data is
    /// >available for the CAISO grid regions.
    ///
    /// [api]: https://jsapi.apiary.io/apis/sgip1/reference/grid-information/marginal-emissions/sgipmoer.html
    #[tracing::instrument(skip(self))]
    pub async fn historic_forecasts(
        &mut self,
        region: GridRegion,
        start: DateTime<Utc>,
        end: DateTime<Utc>,
    ) -> Result<Vec<Forecast>, Error> {
        self.renew().await?;

        let req = self
            .client
            .get("https://sgipsignal.com/sgipforecast/")
            .bearer_auth(self.token.as_ref().expect("recently renewed token"))
            .query(&[
                ("ba", region.to_string()),
                ("starttime", start.to_rfc3339()),
                ("endtime", end.to_rfc3339()),
            ]);

        tracing::debug!(?req);
        let rsp = req.send().await?.text().await?;
        tracing::trace!(?rsp);

        let forecasts = serde_json::from_str(&rsp)?;
        Ok(forecasts)
    }
}

/// An SGIP grid region, corresponding to a balancing authority and independent system operator subregion.
///
/// See the [SGIP Signal grid regions page](https://sgipsignal.com/grid-regions)
/// for details on which electricity providers correspond to which regions.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize)]
#[serde(try_from = "&str")]
#[serde(into = "String")]
pub enum GridRegion {
    /// CAISO San Diego Gas & Electric DLAP
    CAISO_SDGE,
    /// CAISO Pacific Gas & Electric DLAP
    CAISO_PGE,
    /// CAISO Southern California Edison DLAP
    CAISO_SCE,
    /// Los Angeles Department of Water & Power
    LADWP,
    /// BANC Sacramento Municipal Utility District
    BANC_SMUD,
    /// Balancing Authority of Northern California
    BANC_P2,
    /// Imperial Irrigation District
    IID,
    /// PacifiCorp West
    PACW,
    /// NV Energy
    NVENERGY,
    /// Turlock Irrigation District
    TID,
    /// Western Area Lower Colorado
    WALC,
}

impl std::fmt::Display for GridRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            GridRegion::CAISO_SDGE => "SGIP_CAISO_SDGE",
            GridRegion::CAISO_PGE => "SGIP_CAISO_PGE",
            GridRegion::CAISO_SCE => "SGIP_CAISO_SCE",
            GridRegion::LADWP => "SGIP_LADWP",
            GridRegion::BANC_SMUD => "SGIP_BANC_SMUD",
            GridRegion::BANC_P2 => "SGIP_BANC_P2",
            GridRegion::IID => "SGIP_IID",
            GridRegion::PACW => "SGIP_PACW",
            GridRegion::NVENERGY => "SGIP_NVENERGY",
            GridRegion::TID => "SGIP_TID",
            GridRegion::WALC => "SGIP_WALC",
        })
    }
}

impl std::str::FromStr for GridRegion {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "SGIP_CAISO_SDGE" => Ok(GridRegion::CAISO_SDGE),
            "SGIP_CAISO_PGE" => Ok(GridRegion::CAISO_PGE),
            "SGIP_CAISO_SCE" => Ok(GridRegion::CAISO_SCE),
            "SGIP_LADWP" => Ok(GridRegion::LADWP),
            "SGIP_BANC_SMUD" => Ok(GridRegion::BANC_SMUD),
            "SGIP_BANC_P2" => Ok(GridRegion::BANC_P2),
            "SGIP_IID" => Ok(GridRegion::IID),
            "SGIP_PACW" => Ok(GridRegion::PACW),
            "SGIP_NVENERGY" => Ok(GridRegion::NVENERGY),
            "SGIP_TID" => Ok(GridRegion::TID),
            "SGIP_WALC" => Ok(GridRegion::WALC),
            _ => Err(anyhow!("Unknown grid region")),
        }
    }
}

// sadly Rust stabilized FromStr/ToString without TryFrom/Into and they don't
// work with each other.

impl Into<String> for GridRegion {
    fn into(self) -> String {
        self.to_string()
    }
}

impl std::convert::TryFrom<&str> for GridRegion {
    type Error = <GridRegion as FromStr>::Err;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        value.parse()
    }
}

mod serde_help {
    use std::convert::TryFrom;

    use super::*;

    use serde::{de, Deserializer};

    #[derive(Deserialize)]
    #[serde(remote = "Duration")]
    pub struct SecondsDuration(#[serde(getter = "Duration::num_seconds")] i64);

    impl From<SecondsDuration> for Duration {
        fn from(s: SecondsDuration) -> Duration {
            Duration::seconds(s.0)
        }
    }

    // Sometimes the SGIP API returns floats as JSON floats, and sometimes,
    // it returns them as string-encodings of floats. Fun
    pub fn de_f64_from_str<'de, D>(deserializer: D) -> Result<f64, D::Error>
    where
        D: Deserializer<'de>,
    {
        use serde_json::Value;
        Ok(match Value::deserialize(deserializer)? {
            Value::String(s) => s.parse().map_err(de::Error::custom)?,
            Value::Number(num) => num.as_f64().ok_or(de::Error::custom("invalid number"))?,
            _ => return Err(de::Error::custom("wrong type")),
        })
    }

    // This crate represents the forecast data differently and less
    // redundantly than the API; this struct is the raw repr.

    #[derive(Deserialize)]
    pub struct ForecastRaw {
        pub generated_at: DateTime<Utc>,
        pub forecast: Vec<ForecastInner>,
    }

    #[derive(Deserialize)]
    pub struct ForecastInner {
        pub ba: GridRegion,
        pub point_time: DateTime<Utc>,
        #[serde(deserialize_with = "de_f64_from_str")]
        pub value: f64,
    }

    impl TryFrom<ForecastRaw> for Forecast {
        type Error = Error;
        fn try_from(f: ForecastRaw) -> Result<Self, Error> {
            let mut data = BTreeMap::new();
            let generated_at = f.generated_at;
            let region = f
                .forecast
                .first()
                .ok_or_else(|| anyhow!("forecast should have at least one element"))?
                .ba;
            for ForecastInner {
                point_time, value, ..
            } in &f.forecast
            {
                data.insert(*point_time, *value);
            }
            Ok(Forecast {
                generated_at,
                region,
                data,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn init_tracing() {
        let _ = tracing_subscriber::fmt::try_init();
    }

    fn env_creds() -> (String, String) {
        (
            std::env::var("SGIP_SIGNAL_TEST_USER")
                .expect("SGIP_SIGNAL_TEST_USER is unset, please register an account and set the environment variable"),
            std::env::var("SGIP_SIGNAL_TEST_PASS")
                .expect("SGIP_SIGNAL_TEST_PASS is unset, please register an account and set the environment variable"),
        )
    }

    #[tokio::test]
    async fn login() {
        init_tracing();

        let (user, pass) = env_creds();
        let _token = SgipSignal::login(&user, &pass).await.unwrap();
    }

    #[tokio::test]
    async fn pge_moer_latest() {
        init_tracing();

        let (user, pass) = env_creds();
        let mut token = SgipSignal::login(&user, &pass).await.unwrap();

        let latest = token.moer(GridRegion::CAISO_PGE).await.unwrap();

        tracing::info!(?latest);
    }

    #[tokio::test]
    async fn pge_moer_range() {
        init_tracing();

        let (user, pass) = env_creds();
        let mut token = SgipSignal::login(&user, &pass).await.unwrap();

        let start = Utc::now() - Duration::hours(1);

        let _latest = token
            .historic_moers(GridRegion::CAISO_PGE, start, None)
            .await
            .unwrap();
    }

    #[tokio::test]
    async fn pge_forecast() {
        init_tracing();

        let (user, pass) = env_creds();
        let mut token = SgipSignal::login(&user, &pass).await.unwrap();

        let _latest = token.forecast(GridRegion::CAISO_PGE).await.unwrap();
    }

    #[tokio::test]
    async fn pge_historic_forecasts() {
        init_tracing();

        let (user, pass) = env_creds();
        let mut token = SgipSignal::login(&user, &pass).await.unwrap();

        let start = Utc::now() - Duration::hours(2);
        let end = Utc::now() - Duration::hours(1);

        let _latest = token
            .historic_forecasts(GridRegion::CAISO_PGE, start, end)
            .await
            .unwrap();
    }

    #[tokio::test]
    async fn check_forecast_error() {
        init_tracing();

        let (user, pass) = env_creds();
        let mut token = SgipSignal::login(&user, &pass).await.unwrap();

        let current_moer = token.moer(GridRegion::CAISO_PGE).await.unwrap();
        let now = current_moer.start;

        let t_minus_1h = now - Duration::hours(1);
        let t_minus_6h = now - Duration::hours(6);
        let t_minus_12h = now - Duration::hours(12);
        let t_minus_24h = now - Duration::hours(24);

        // Chosen so that [t, t+delta) overlaps with at least one forecast
        let delta = Duration::minutes(6);

        let forecast_1h_ago = token
            .historic_forecasts(GridRegion::CAISO_PGE, t_minus_1h, t_minus_1h + delta)
            .await
            .unwrap()
            .pop()
            .unwrap();
        let forecast_6h_ago = token
            .historic_forecasts(GridRegion::CAISO_PGE, t_minus_6h, t_minus_6h + delta)
            .await
            .unwrap()
            .pop()
            .unwrap();
        let forecast_12h_ago = token
            .historic_forecasts(GridRegion::CAISO_PGE, t_minus_12h, t_minus_12h + delta)
            .await
            .unwrap()
            .pop()
            .unwrap();
        let forecast_24h_ago = token
            .historic_forecasts(GridRegion::CAISO_PGE, t_minus_24h, t_minus_24h + delta)
            .await
            .unwrap()
            .pop()
            .unwrap();

        let moer_1h_backtest = forecast_1h_ago.at(now).unwrap();
        let moer_6h_backtest = forecast_6h_ago.at(now).unwrap();
        let moer_12h_backtest = forecast_12h_ago.at(now).unwrap();
        let moer_24h_backtest = forecast_24h_ago.at(now).unwrap();

        tracing::info!(?current_moer);
        tracing::info!(?moer_1h_backtest);
        tracing::info!(?moer_6h_backtest);
        tracing::info!(?moer_12h_backtest);
        tracing::info!(?moer_24h_backtest);

        let delta_1h = moer_1h_backtest.rate - current_moer.rate;
        let delta_6h = moer_6h_backtest.rate - current_moer.rate;
        let delta_12h = moer_12h_backtest.rate - current_moer.rate;
        let delta_24h = moer_24h_backtest.rate - current_moer.rate;

        tracing::info!(?delta_1h, ?delta_6h, ?delta_12h, ?delta_24h);
    }

    #[test]
    fn moer_deserialize() {
        init_tracing();
        let s = r#"[{"point_time": "2021-02-14T01:30:00+00:00", "moer": 0.483309471658446, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T01:25:00+00:00", "moer": 0.438266316771232, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T01:20:00+00:00", "moer": 0.408947385825297, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T01:15:00+00:00", "moer": 0.368624537685765, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T01:10:00+00:00", "moer": 0.389189897375465, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T01:05:00+00:00", "moer": 0.420874665179944, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T01:00:00+00:00", "moer": 0.398493981636107, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:55:00+00:00", "moer": 0.497525279919501, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:50:00+00:00", "moer": 0.51071504648925, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:45:00+00:00", "moer": 0.546918718439869, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:40:00+00:00", "moer": 0.574789397002207, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:35:00+00:00", "moer": 0.467521379165322, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:30:00+00:00", "moer": 0.574789397002207, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:25:00+00:00", "moer": 0.567860381337691, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:20:00+00:00", "moer": 0.335962461716266, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:15:00+00:00", "moer": 0.266455453439315, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:10:00+00:00", "moer": 0.226338215564035, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:05:00+00:00", "moer": 0.100627509672054, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}, {"point_time": "2021-02-14T00:00:00+00:00", "moer": 0.176600565113808, "version": "1.0", "freq": 300, "ba": "SGIP_CAISO_PGE"}]"#;

        let _moers: Vec<Moer> = serde_json::from_str(s).unwrap();
    }
}
