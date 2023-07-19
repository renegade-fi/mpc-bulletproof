//! Defines helpers for integration testing

use futures::Future;
use mpc_stark::algebra::scalar::Scalar;
use tokio::runtime::Handle;

/// Block the current thread on a future
pub fn await_result<T, F: Future<Output = T>>(future: F) -> T {
    Handle::current().block_on(future)
}

/// Assert two values are equal, returning a `String` error if they are not
pub fn assert_scalars_eq(a: &Scalar, b: &Scalar) -> Result<(), String> {
    if a != b {
        Err(format!("expected {:?} == {:?}", a, b))
    } else {
        Ok(())
    }
}
