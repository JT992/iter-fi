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
    ///
    /// # Examples
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let something = ('a'..'f')
    ///     .map_if(true, |c| c as u8)
    ///     .branched()
    ///     .as_true()
    ///     .unwrap()
    ///     .collect::<Vec<_>>();
    /// assert_eq!(something, vec![97, 98, 99, 100, 101]);
    ///
    /// let something_else = (0..5)
    ///     .map_if(false, |c| c as u8)
    ///     .branched()
    ///     .as_true();
    /// assert!(something_else.is_none());
    /// ```
    pub fn as_true(self) -> Option<T> {
        match self.0 {
            IterIf::True(t) => Some(t),
            IterIf::False(_) => None,
        }
    }

    /// Return `Some(F)` if the condition was false and `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let something = ('a'..'f')
    ///     .map_if(false, |c| c as u8)
    ///     .branched()
    ///     .as_false()
    ///     .unwrap()
    ///     .collect::<Vec<_>>();
    /// assert_eq!(something, vec!['a', 'b', 'c', 'd', 'e']);
    ///
    /// let something_else = (0..5)
    ///     .map_if(true, |c| c as u8)
    ///     .branched()
    ///     .as_false();
    /// assert!(something_else.is_none());
    /// ```
    pub fn as_false(self) -> Option<F> {
        match self.0 {
            IterIf::True(_) => None,
            IterIf::False(f) => Some(f),
        }
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
