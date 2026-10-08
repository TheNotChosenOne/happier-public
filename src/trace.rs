#[cfg(feature = "trace")]
macro_rules! trace_at {
    ($target:expr, $($arg:tt)*) => {
        ::tracing::event!(target: $target, ::tracing::Level::TRACE, $($arg)*)
    };
}

#[cfg(not(feature = "trace"))]
macro_rules! trace_at {
    ($target:expr, $($arg:tt)*) => {
        if false {
            let _unused = format_args!($($arg)*);
        }
    };
}

macro_rules! trace_assign {
    ($($arg:tt)*) => { trace_at!("happier::assign", $($arg)*) };
}

macro_rules! trace_flow {
    ($($arg:tt)*) => { trace_at!("happier::flow", $($arg)*) };
}

macro_rules! trace_learn {
    ($($arg:tt)*) => { trace_at!("happier::learn", $($arg)*) };
}

#[cfg_attr(not(feature = "trace"), allow(unused_macros))]
macro_rules! trace_stats {
    ($($arg:tt)*) => { trace_at!("happier::stats", $($arg)*) };
}

macro_rules! tracing_enabled {
    ($target:expr) => {{
        #[cfg(feature = "trace")]
        {
            ::tracing::enabled!(target: $target, ::tracing::Level::TRACE)
        }
        #[cfg(not(feature = "trace"))]
        {
            false
        }
    }};
}
