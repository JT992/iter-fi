Boolean composable iterators.

This crate adds the `iter_if` method to all `Iterator`s.
If its `condition` is `true`, it calls a function and returns its result.
Otherwise, it returns `self`.

## Is this useful?

I have no idea. I made this because I had kind-of-a-use-case for `IterIf`.
