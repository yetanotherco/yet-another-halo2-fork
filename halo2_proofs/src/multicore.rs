#[cfg(all(
    feature = "multicore",
    target_arch = "wasm32",
    not(target_feature = "atomics")
))]
compile_error!(
    "The multicore feature flag is not supported on wasm32 architectures without atomics"
);

pub use maybe_rayon::{
    iter::{
        IndexedParallelIterator, IntoParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
    },
    join, scope, Scope,
};

#[cfg(feature = "multicore")]
pub use maybe_rayon::{
    current_num_threads, iter::IntoParallelRefIterator, slice::ParallelSliceMut,
};

#[cfg(not(feature = "multicore"))]
pub fn current_num_threads() -> usize {
    1
}

pub trait TryFoldAndReduce<T, E> {
    /// Implements `iter.try_fold().try_reduce()` for `rayon::iter::ParallelIterator`,
    /// falling back on `Iterator::try_fold` when the `multicore` feature flag is
    /// disabled.
    /// The `try_fold_and_reduce` function can only be called by a iter with
    /// `Result<T, E>` item type because the `fold_op` must meet the trait
    /// bounds of both `try_fold` and `try_reduce` from rayon.   
    fn try_fold_and_reduce(
        self,
        identity: impl Fn() -> T + Send + Sync,
        fold_op: impl Fn(T, Result<T, E>) -> Result<T, E> + Send + Sync,
    ) -> Result<T, E>;
}

impl<T, E, I> TryFoldAndReduce<T, E> for I
where
    T: Send + Sync,
    E: Send + Sync,
    I: maybe_rayon::iter::ParallelIterator<Item = Result<T, E>>,
{
    fn try_fold_and_reduce(
        self,
        identity: impl Fn() -> T + Send + Sync,
        fold_op: impl Fn(T, Result<T, E>) -> Result<T, E> + Send + Sync,
    ) -> Result<T, E> {
        self.try_fold(&identity, &fold_op)
            .try_reduce(&identity, |a, b| fold_op(a, Ok(b)))
    }
}
