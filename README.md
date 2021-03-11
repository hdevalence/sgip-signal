Unofficial Rust bindings to the [SGIP Signal API][sgipsignal],
which provides access to real-time and forecasted marginal Greenhouse Gas
(GHG) emissions data for participants in California's Self Generation
Incentive Program (SGIP).

More information is available on the [SGIP Signal website][sgipsignal]:

> Further details about SGIP itself can be found on the
> [SGIP website][sgipwebsite]. The SGIP
> program is implementing new GHG requirements, which are explained in the
> [SGIP Handbook][sgiphandbook]. This website provides data which will
> assist energy storage developers, operators, and others in implementing
> those rules.

The API reports GHG emissions data in the form of Marginal Operating
Emissions Rates (MOERs), represented in this crate by the [`Moer`] type.
Forecasted MOERs are represented by the [`Forecast`] type, whose
[`Forecast::at`] method allows querying forecasted data. API calls are
performed using the [`SgipSignal`] type, which represents an authenticated
session with the API and automatically handles credential lifetimes and
periodic reauthentication.

This crate currently supports the following subset of the API:

- ☐ user registration (use a one-off `curl` command for now);
- ☑ user authentication and session management, using the [`SgipSignal`] type;
- ☑ current MOER data, using [`SgipSignal::moer`];
- ☑ historical MOER data, using [`SgipSignal::historic_moers`];
- ☑ current short-term (72-hour) MOER forecasts, using [`SgipSignal::forecast`];
- ☑ historical short-term (72-hour) MOER forecasts, using [`SgipSignal::historic_forecasts`];
- ☐ current long-term (1-month and 1-year) MOER forecasts;
- ☐ historical long-term (1-month and 1-year) MOER forecasts;
- ☐ rate limiting and backpressure;

This is an unofficial set of bindings, with no guarantees about maintenance
or functional correctness.

[sgipsignal]: https://sgipsignal.com/
[sgipwebsite]: https://www.selfgenca.com/
[sgiphandbook]: https://www.selfgenca.com/home/resources/