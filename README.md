# An attempt to formalise Beautiful Folding more polymorphically

[Beautiful Folding][beauty] with more polymorphic combinators, inspired by [`foldl`][foldl] and [`folds`][folds].

## Goals

- Uniform treatment of pure/impure folds
- Type-level distinction between possibly-empty and non-empty (or, monoid vs. semigroup, resp.) folds
  * Example: We should safely expect the inner fold of `foldByKeyMap`-like folds:
  
    ```hs
    foldByKeyMap :: forall k a b m l. (Monad m, Ord k) => FolderM L1 m a b -> FolderM l m (k, a) (Map k b)
    ```
  
  * We can still use monoidal folds in place of semigroup folds.

[beauty]: http://squing.blogspot.com/2008/11/beautiful-folding.html
[foldl]: https://hackage.haskell.org/package/foldl
[folds]: https://hackage.haskell.org/package/folds
