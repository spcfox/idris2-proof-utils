module Control.Traversable.LawfulTraversable

import public Control.Functor.LawfulFoldableFunctor
import public Control.Applicative.LawfulApplicative

%default total

public export
record LawfulTraversable t {auto 0 traversable : Traversable t} where
  [search traversable]
  constructor MkLawfulTraversable

  lawfulFoldableFunctor : LawfulFoldableFunctor t

  commTraverseToList : forall f, a, b. (0 _ : Applicative f) => LawfulApplicative f =>
                       (g : a -> f b) -> (xs : t a) ->
                       (Prelude.toList <$> traverse g xs) === traverse g (toList xs)

public export
commTraverseToList : (0 _ : Traversable t) => LawfulTraversable t =>
                     (0 _ :Applicative f) => LawfulApplicative f =>
                     (g : a -> f b) -> (xs : t a) -> (Prelude.toList <$> traverse g xs) === traverse g (toList xs)
commTraverseToList = %search.commTraverseToList
