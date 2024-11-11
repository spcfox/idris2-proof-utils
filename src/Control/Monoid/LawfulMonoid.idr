module Control.Monoid.LawfulMonoid

import public Control.Semigroup.LawfulSemigroup

%default total

public export
record LawfulMonoid m {auto 0 monoid : Monoid m} where
  [search monoid]
  constructor MkLawfulMonoid
  lawfulSemigroup : LawfulSemigroup m
  identityLeftLaw : (x : m) -> Prelude.neutral <+> x === x
  identityRightLaw : (x : m) -> x <+> Prelude.neutral === x

public export
identityLeftLaw : (0 _ : Monoid m) => LawfulMonoid m => (x : m) -> Prelude.neutral <+> x === x
identityLeftLaw = %search.identityLeftLaw

public export
identityRightLaw : (0 _ : Monoid m) => LawfulMonoid m => (x : m) -> x <+> Prelude.neutral === x
identityRightLaw = %search.identityRightLaw
