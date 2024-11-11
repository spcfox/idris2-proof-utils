module Control.Functor.LawfulFoldableFunctor

import public Control.Monoid.LawfulMonoid
import public Control.Functor.LawfulFunctor
import public Control.Foldable.LawfulFoldable

%default total

public export
record LawfulFoldableFunctor t {auto 0 functor : Functor t} {auto 0 foldable : Foldable t} where
  [search foldable]
  constructor MkLawfulFoldableFunctor
  lawfulFunctor : LawfulFunctor t
  lawfulFoldable : LawfulFoldable t

  commMapToList : forall a, b. (0 f : a -> b) -> (xs : t a) ->
                  toList (map f xs) === map f (toList xs)

public export
commMapToList : (0 _ : Functor t) => (0 _ : Foldable t) => LawfulFoldableFunctor t =>
                (0 f : a -> b) -> (xs : t a) -> toList (map f xs) === map f (toList xs)
commMapToList = %search.commMapToList
