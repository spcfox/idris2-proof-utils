module Data.List.Properties

import public Control.Functor.LawfulFoldableFunctor

%default total

public export %hint
lawfulFunctor : LawfulFunctor List
lawfulFunctor = MkLawfulFunctor identityLaw compLaw
where
  identityLaw : (xs : List a) -> xs === map Prelude.id xs
  identityLaw []              = Refl
  identityLaw (x :: xs) = cong (x ::) $ identityLaw xs

  compLaw : (xs : List a) -> map g (map f xs) === map (g . f) xs
  compLaw []        = Refl
  compLaw (x :: xs) = cong (g (f x) ::) $ compLaw xs

public export %hint
lawfulFoldableList : LawfulFoldable List
lawfulFoldableList = MkLawfulFoldable
  { foldMapLaw = \_ => Refl
  , foldrLaw   = \_ => Refl
  , foldlLaw   = \_ => Refl
  , nullLaw    = \_ => Refl
  }

public export %hint
lawfulFoldableFunctorList : LawfulFoldableFunctor List
lawfulFoldableFunctorList = MkLawfulFoldableFunctor %search %search $ \_, _ => Refl
