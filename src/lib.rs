//! Boolean composable iterators.
//!
//! This crate adds the [`iter_if`] method to all [`Iterator`]s.
//! If its `condition` is `true`, it calls a function and returns its result.
//! Otherwise, it returns `self`.
//!
//! ## Is this useful?
//!
//! I have no idea. I made this because I had kind-of-a-use-case for `IterIf`.
//!
//! ## Crate features
//!
//! Both features are enabled by default.
//!
//! - `branched`: allows iteration over iterators with two different types and adds a dependency
//!   on [`either`]
//! - `std`: disabling this will make the crate `#[no_std]`
//!
//! [`iter_if`]: crate::IterFi::iter_if
#![warn(clippy::pedantic)]
#![warn(clippy::perf)]
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

mod branching;

#[cfg(feature = "branched")]
pub use branching::Branched;

use core::iter::Map;

/// Boolean composable iterators.
///
/// This trait adds the [`iter_if`] method which takes a boolean condition and a function.
/// If the condition is met, the function is run and the returned iterator is used as output.
/// Otherwise, the call is ignored and the original iterator continues.
///
/// This trait has an automatic blanket implementation for all [`Iterator`]s.
/// You do not need to implement it on your own iterators.
///
/// [`iter_if`]: crate::IterFi::iter_if
pub trait IterFi: Iterator {
    /// If `condition` is `true`, return the iterator returned by `func`.
    /// Otherwise, skip this call and return `self`.
    ///
    /// Note that if [`T::Item`] is not the same as `F::Item`, you will need to call [`branched`]
    /// after this to get an iterator.
    ///
    /// # Examples
    ///
    /// When the condition is true, the function is applied:
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let numbers = (0..5).iter_if(true, Iterator::rev).collect::<Vec<_>>();
    /// assert_eq!(numbers, vec![4, 3, 2, 1, 0]);
    /// ```
    ///
    /// When the condition is false, the function is ignored:
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let numbers = (0..5).iter_if(false, Iterator::rev).collect::<Vec<_>>();
    /// assert_eq!(numbers, vec![0, 1, 2, 3, 4]);
    /// ```
    ///
    /// [`T::Item`]: Iterator::Item
    /// [`branched`]: IterIf::branched
    fn iter_if<C, T: Iterator>(self, condition: bool, func: C) -> IterIf<T, Self>
    where
        Self: Sized,
        C: Fn(Self) -> T,
    {
        if condition {
            IterIf::True(func(self))
        } else {
            IterIf::False(self)
        }
    }

    /// If `condition` is `true`, apply `func` to elements in `self`.
    /// Otherwise, skip this call and return `self`.
    ///
    /// This is a shorthand for `iter_if(condition, |i| i.map(func))`.
    /// See the documentation for [`iter_if`] for more.
    ///
    /// # Examples
    ///
    /// When the condition is true, the map is applied:
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let numbers = (0..5).map_if(true, |n| n * 2).collect::<Vec<_>>();
    /// assert_eq!(numbers, vec![0, 2, 4, 6, 8]);
    /// ```
    ///
    /// When the condition is false, the map is ignored:
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let numbers = (0..5).map_if(false, |n| n * 2).collect::<Vec<_>>();
    /// assert_eq!(numbers, vec![0, 1, 2, 3, 4]);
    /// ```
    ///
    /// [`iter_if`]: IterFi::iter_if
    fn map_if<C, T>(self, condition: bool, func: C) -> IterIf<Map<Self, C>, Self>
    where
        Self: Sized,
        C: Fn(Self::Item) -> T,
    {
        if condition {
            IterIf::True(self.map(func))
        } else {
            IterIf::False(self)
        }
    }
}

impl<I: Iterator> IterFi for I {}

/// An iterator which yields items from `T` if the original condition was true
/// and `F` if not.
///
/// This struct is created by the [`iter_if`] method on [`IterFi`]. See its documentation for more.
///
/// [`iter_if`]: crate::IterFi::iter_if
/// [`IterFi`]: crate::IterFi
#[derive(Debug, Clone, Copy)]
pub enum IterIf<T: Iterator, F: Iterator> {
    /// Variant if the original condition was true.
    True(T),
    /// Variant if the original condition was false.
    False(F),
}

impl<T: Iterator<Item = I>, F: Iterator<Item = I>, I> Iterator for IterIf<T, F> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IterIf::True(t) => t.next(),
            IterIf::False(f) => f.next(),
        }
    }
}

impl<T: Iterator, F: Iterator> IterIf<T, F> {
    /// Convert this boolean iterator to a branched iterator.
    ///
    /// The `Branched` iterator can iterate over two different types.
    /// It is only useful if the two iterators have different [`Iterator::Item`]s.
    /// If they are the same, you can iterate directly over the [`IterIf`].
    ///
    /// # Examples
    ///
    /// ```
    /// use iter_fi::IterFi;
    /// use either::Either;
    ///
    /// let mut something = ('a'..'f')
    ///     .map_if(true, |c| c as u8)
    ///     .branched();
    /// assert_eq!(something.next(), Some(Either::Left(97)));
    /// assert_eq!(something.next(), Some(Either::Left(98)));
    ///
    /// let mut something_else = ('a'..'f')
    ///     .map_if(false, |c| c as u8)
    ///     .branched();
    /// assert_eq!(something_else.next(), Some(Either::Right('a')));
    /// assert_eq!(something_else.next(), Some(Either::Right('b')));
    /// ```
    #[cfg(feature = "branched")]
    pub fn branched(self) -> Branched<T, F> {
        Branched(self)
    }

    /// If the original condition was false, apply `func` to the iterator. Otherwise, pass.
    ///
    /// # Examples
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let some_numbers = (0..5)
    ///     .iter_if(true, Iterator::rev)
    ///     .else_iter(|i| i.skip(3))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(some_numbers, vec![4, 3, 2, 1, 0]);
    ///
    /// let some_more_numbers = (0..5)
    ///     .iter_if(false, Iterator::rev)
    ///     .else_iter(|i| i.skip(3))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(some_more_numbers, vec![3, 4]);
    /// ```
    pub fn else_iter<C, N: Iterator>(self, func: C) -> IterIf<T, N>
    where
        C: Fn(F) -> N,
    {
        match self {
            Self::True(t) => IterIf::True(t),
            Self::False(f) => IterIf::False(func(f)),
        }
    }

    /// If the original condition was false, map `func` over the iterator. Otherwise, pass.
    ///
    /// # Examples
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let some_numbers = (0..5)
    ///     .map_if(true, |n| n * 2)
    ///     .else_map(|n| n + 3)
    ///     .collect::<Vec<_>>();
    /// assert_eq!(some_numbers, vec![0, 2, 4, 6, 8]);
    ///
    /// let some_more_numbers = (0..5)
    ///     .map_if(false, |n| n * 2)
    ///     .else_map(|n| n + 3)
    ///     .collect::<Vec<_>>();
    /// assert_eq!(some_more_numbers, vec![3, 4, 5, 6, 7]);
    /// ```
    ///
    /// [`else_iter`]: IterIf::else_iter
    pub fn else_map<C, N>(self, func: C) -> IterIf<T, Map<F, C>>
    where
        C: Fn(F::Item) -> N,
    {
        match self {
            Self::True(t) => IterIf::True(t),
            Self::False(f) => IterIf::False(f.map(func)),
        }
    }

    /// Return `Some(T)` if the condition was true and `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use iter_fi::IterFi;
    ///
    /// let numbers = (0..5)
    ///     .iter_if(true, Iterator::rev)
    ///     .as_true()
    ///     .unwrap()
    ///     .collect::<Vec<_>>();
    /// assert_eq!(numbers, vec![4, 3, 2, 1, 0]);
    ///
    /// let more_numbers = (0..5)
    ///     .iter_if(false, Iterator::rev)
    ///     .as_true();
    /// assert!(more_numbers.is_none());
    /// ```
    pub fn as_true(self) -> Option<T> {
        match self {
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
    /// let numbers = (0..5)
    ///     .iter_if(false, Iterator::rev)
    ///     .as_false()
    ///     .unwrap()
    ///     .collect::<Vec<_>>();
    /// assert_eq!(numbers, vec![0, 1, 2, 3, 4]);
    ///
    /// let more_numbers = (0..5)
    ///     .iter_if(true, Iterator::rev)
    ///     .as_false();
    /// assert!(more_numbers.is_none());
    /// ```
    pub fn as_false(self) -> Option<F> {
        match self {
            IterIf::True(_) => None,
            IterIf::False(f) => Some(f),
        }
    }
}
