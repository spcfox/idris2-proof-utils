module Data.Pair.Properties

import public Control.Traversable.LawfulTraversable

import Syntax.PreorderReasoning

%default total

public export %hint
lawfulFunctorPair : LawfulFunctor (Pair a)
lawfulFunctorPair = MkLawfulFunctor
  { identityLaw = \(_, _) => Refl
  , compLaw     = \(_, _) => Refl
  }

public export %hint
lawfulLawfulFoldable : LawfulFoldable (Pair a)
lawfulLawfulFoldable = MkLawfulFoldable
  { foldMapLaw = \(_, _) => identityRightLaw _ `trans` sym (identityLeftLaw _)
  , foldrLaw   = \(_, _) => Refl
  , foldlLaw   = \(_, _) => Refl
  , nullLaw    = \(_, _) => Refl
  }

public export %hint
lawfulFoldableFunctorPair : LawfulFoldableFunctor (Pair a)
lawfulFoldableFunctorPair = MkLawfulFoldableFunctor %search %search $ \_, (_, _) => Refl

public export %hint
lawfulTraversablePair : LawfulTraversable (Pair a)
lawfulTraversablePair = MkLawfulTraversable %search commTraverseToList
where
  commTraverseToList : (0 _ : Applicative f) => LawfulApplicative f =>
                       (g : b -> f c) -> (xs : (a, b)) ->
                       map Prelude.toList (traverse g xs) === traverse g (toList xs)
  commTraverseToList f (x, y) =
    Calc $
      |~ map toList (traverse f (x, y))
      ~~ map toList (map (x,) $ f y)   ...( Refl )
      ~~ map (:: []) (f y)             ...( compLaw @{%search} @{lawfulFunctor} _ ) -- TODO: %search can't find `lawfulFunctor`
      ~~ pure (:: []) <*> f y          ...( sym $ mapApplicativeLaw _ )
      ~~ pure (::) <*> f y <*> pure [] ...( sym $ interchange2Law _ )
      ~~ traverse f (toList (x, y))    ...( Refl )
