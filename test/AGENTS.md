# Characterization and runtime tests

Preserve existing fade and parameter tests. Test observable ordering, lifecycle,
channel bytes and state ownership using actual code. Do not fake whole required
namespaces to hide dependency problems. Constructors may be tested without
starting shows or opening output devices. Close injected worker pools in finally;
use latches or controlled clocks rather than timing sleeps for concurrency tests.
Keep pure and legacy lanes explicit in dev/afterglow/test_runner.clj.
