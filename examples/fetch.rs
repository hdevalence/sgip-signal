use chrono::{Duration, Utc};
use chrono_tz::US::Pacific;
use hdrhistogram::Histogram;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use structopt::StructOpt;

use sgip_signal::{GridRegion, Moer, SgipSignal};

#[derive(Debug, StructOpt)]
#[structopt(name = "fetch", about = "fetch MOER data")]
struct Opt {
    /// The SGIP Signal username
    #[structopt(short, long)]
    username: String,

    /// The SGIP Signal password
    #[structopt(short, long)]
    password: String,

    #[structopt(subcommand)]
    cmd: Cmd,
}

#[derive(Debug, StructOpt)]
enum Cmd {
    /// Dump a timeline of actual MOER data with PST timestamps
    Timeline {
        /// Number of days to request (max 31)
        #[structopt(short, long)]
        days: u32,
    },
    /// Dump a timeline of actual MOER data averaged by day with PST timestamps
    DailyAverage {
        /// Number of days to request (max 31)
        #[structopt(short, long)]
        days: u32,
    },
    /// Dump the forecast issued some hours ago, with PST timestamps
    Forecast {
        /// The number of hours ago the forecast was issued
        #[structopt(short, long)]
        hours: u32,
    },
}

#[derive(Serialize, Deserialize)]
struct TimelineRecord {
    datetime: String,
    rate: f64,
}

impl From<Moer> for TimelineRecord {
    fn from(m: Moer) -> TimelineRecord {
        TimelineRecord {
            rate: m.rate,
            datetime: m.start.with_timezone(&Pacific).to_rfc3339(),
        }
    }
}

#[derive(Serialize, Deserialize)]
struct DailyAverageRecord {
    time: chrono::NaiveTime,
    mean: f64,
    min: f64,
    p10: f64,
    p25: f64,
    median: f64,
    p75: f64,
    p90: f64,
    max: f64,
}

fn daily_averages(moers: Vec<Moer>) -> Vec<DailyAverageRecord> {
    let mut by_time = BTreeMap::new();
    for m in moers.into_iter() {
        let local_time = m.start.with_timezone(&Pacific).time();
        by_time
            .entry(local_time)
            .or_insert(Histogram::<u64>::new(3).unwrap())
            .record((m.rate * 1000.) as u64)
            .unwrap();
    }

    by_time
        .into_iter()
        .map(|(time, rates)| {
            let min = rates.min() as f64 / 1000.;
            let max = rates.max() as f64 / 1000.;
            let mean = rates.mean() as f64 / 1000.;
            let p10 = rates.value_at_quantile(0.1) as f64 / 1000.;
            let p25 = rates.value_at_quantile(0.25) as f64 / 1000.;
            let median = rates.value_at_quantile(0.5) as f64 / 1000.;
            let p75 = rates.value_at_quantile(0.75) as f64 / 1000.;
            let p90 = rates.value_at_quantile(0.90) as f64 / 1000.;
            DailyAverageRecord {
                time,
                min,
                max,
                mean,
                median,
                p10,
                p25,
                p75,
                p90,
            }
        })
        .collect()
}

#[tokio::main]
async fn main() {
    let opt = Opt::from_args();
    tracing::info!(?opt);

    let mut token = SgipSignal::login(&opt.username, &opt.password)
        .await
        .unwrap();

    match opt.cmd {
        Cmd::Timeline { days } => {
            let moers = token
                .historic_moers(
                    GridRegion::CAISO_PGE,
                    Utc::now() - Duration::days(days as i64),
                    None,
                )
                .await
                .unwrap();
            let mut writer = csv::Writer::from_writer(std::io::stdout());
            for m in moers.into_iter() {
                writer.serialize(TimelineRecord::from(m)).unwrap();
            }
        }
        Cmd::DailyAverage { days } => {
            let moers = token
                .historic_moers(
                    GridRegion::CAISO_PGE,
                    Utc::now() - Duration::days(days as i64),
                    None,
                )
                .await
                .unwrap();
            let mut writer = csv::Writer::from_writer(std::io::stdout());
            let records = daily_averages(moers);
            for r in records.into_iter() {
                writer.serialize(r).unwrap();
            }
        }
        Cmd::Forecast { hours } => {
            let forecast_time = Utc::now() - Duration::hours(hours as i64);

            let forecast = token
                .historic_forecasts(
                    GridRegion::CAISO_PGE,
                    forecast_time,
                    forecast_time + Duration::minutes(6),
                )
                .await
                .unwrap()
                .remove(0);

            let mut writer = csv::Writer::from_writer(std::io::stdout());
            for m in forecast.moers() {
                writer.serialize(TimelineRecord::from(m)).unwrap();
            }
        }
    }
}
