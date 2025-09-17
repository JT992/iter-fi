#![cfg(feature = "branched")]

use either::Either;

use crate::IterIf;

/// An iterator which yields `T::Item` if the original condition was true
/// and `F::Item` if not.
///
/// This struct is created by the [`branched`] method on [`IterIf`]. See its documentation for more.
///
/// [`branched`]: IterIf::branched
#[derive(Debug, Clone, Copy)]
pub struct Branched<T: Iterator, F: Iterator>(pub IterIf<T, F>);

impl<T: Iterator, F: Iterator> Iterator for Branched<T, F> {
    type Item = Either<T::Item, F::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            IterIf::True(t) => Some(Either::Left(t.next()?)),
            IterIf::False(f) => Some(Either::Right(f.next()?)),
        }
    }
}

impl<T: Iterator, F: Iterator> Branched<T, F> {
    /// Return `Some(T)` if the condition was true and `None` otherwise.
    pub fn as_true(self) -> Option<T> {
        match self.0 {
            IterIf::True(t) => Some(t),
            IterIf::False(_) => None,
        }
    }

    /// Return `Some(F)` if the condition was false and `None` otherwise.
    pub fn as_false(self) -> Option<F> {
        match self.0 {
            IterIf::True(_) => None,
            IterIf::False(f) => Some(f),
        }
    }

    /// True if the condition was true.
    pub fn is_true(&self) -> bool {
        matches!(self.0, IterIf::True(_))
    }

    /// True if the condition was false.
    pub fn is_false(&self) -> bool {
        matches!(self.0, IterIf::False(_))
    }
}

impl<T: Iterator<Item = I>, F: Iterator<Item = I>, I> Branched<T, F> {
    /// Unwrap this branched iterator, returning the original [`IterIf`].
    ///
    /// The only difference between `self.unbranch()` and `self.0` is that
    /// `unbranch` can only be called if the [`Iterator::Item`] types are the same.
    /// This might be useful if a previously branched iterator now has two identical types and can
    /// be merged.
    ///
    /// [`branched`]: IterIf::branched
    pub fn unbranch(self) -> IterIf<T, F> {
        self.0
    }
}
