module Control.Foldable.LawfulFoldable

import Control.Monoid.LawfulMonoid

%default total

public export
record LawfulFoldable t {auto 0 foldable : Foldable t} where
  [search foldable]
  constructor MkLawfulFoldable
  foldMapLaw : forall m, a. (0 _ : Monoid m) => LawfulMonoid m =>
               {0 f : a -> m} -> (xs : t a) ->
               foldMap f xs === foldMap f (toList xs)

  foldrLaw : forall a, acc. {0 f : a -> acc -> acc} -> {0 z : acc} ->
             (xs : t a) -> foldr f z xs === foldr f z (toList xs)

  foldlLaw : forall a, acc. {0 f : acc -> a -> acc} -> {0 z : acc} ->
             (xs : t a) -> foldl f z xs === foldl f z (toList xs)

  nullLaw : forall a. (xs : t a) -> null xs === null (toList xs)

public export
foldMapLaw : (0 _ : Foldable t) => LawfulFoldable t => (0 _ : Monoid m) => LawfulMonoid m =>
             {0 f : a -> m} -> (xs : t a) -> foldMap f xs === foldMap f (toList xs)
foldMapLaw = %search.foldMapLaw

public export
foldrLaw : (0 _ : Foldable t) => LawfulFoldable t =>
           (xs : t a) -> foldr f z xs === foldr f z (toList xs)
foldrLaw = %search.foldrLaw

public export
foldlLaw : (0 _ : Foldable t) => LawfulFoldable t =>
           (xs : t a) -> foldl f z xs === foldl f z (toList xs)
foldlLaw = %search.foldlLaw

public export
nullLaw : (0 _ : Foldable t) => LawfulFoldable t =>
          (xs : t a) -> null xs === null (toList xs)
nullLaw = %search.nullLaw
