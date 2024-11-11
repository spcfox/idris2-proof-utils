module Control.Semigroup.LawfulSemigroup

%default total

public export
record LawfulSemigroup m {auto 0 semigroup : Semigroup m} where
  [search semigroup]
  constructor MkLawfulSemigroup
  assocLaw : (x, y, z : m) -> x <+> (y <+> z) === (x <+> y) <+> z

public export
assocLaw : (0 _ : Semigroup m) => LawfulSemigroup m =>
           (x, y, z : m) -> x <+> (y <+> z) === (x <+> y) <+> z
assocLaw = %search.assocLaw
