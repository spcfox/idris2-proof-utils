module Data.CheckedEmpty.List.Lazy.Properties

import Data.CheckedEmpty.List.Lazy

import Data.So.Utils
import Data.Maybe

import Control.Foldable.Elem
import Control.Foldable.Quantifiers
import public Control.Functor.LawfulFoldableFunctor
import Syntax.WithProof.Extra

%default total

public export %hint
lawfulFunctorLazyLst : LawfulFunctor $ LazyLst ne
lawfulFunctorLazyLst = MkLawfulFunctor identityLaw compLaw
where
  identityLaw : (xs : LazyLst em a) -> xs === map Prelude.id xs
  identityLaw []              = Refl
  identityLaw (x :: Delay xs) = cong (x ::) $ identityLaw xs

  compLaw : (xs : LazyLst em a) -> map g (map f xs) === map (g . f) xs
  compLaw []        = Refl
  compLaw (x :: xs) = cong (g (f x) ::) $ compLaw xs

public export %hint
lawfulFoldableLazyLst : LawfulFoldable $ LazyLst ne
lawfulFoldableLazyLst = MkLawfulFoldable
  { foldMapLaw = foldlLaw
  , foldrLaw   = foldrLaw
  , foldlLaw   = foldlLaw
  , nullLaw    = nullLaw
  }
where
  foldrLaw : (xs : LazyLst em a) -> foldr f z xs === foldr f z (toList xs)
  foldrLaw []        = Refl
  foldrLaw (x :: xs) = cong (f x) $ foldrLaw xs

  foldlLaw : (xs : LazyLst em a) -> foldl f z xs === foldl f z (toList xs)
  foldlLaw []        = Refl
  foldlLaw (x :: xs) = foldlLaw xs

  nullLaw : (xs : LazyLst em a) -> null xs === null (toList xs)
  nullLaw []       = Refl
  nullLaw (_ :: _) = Refl

public export %hint
lawfulFoldableFunctorLst : LawfulFoldableFunctor $ LazyLst ne
lawfulFoldableFunctorLst = MkLawfulFoldableFunctor %search %search commMapToList
where
  commMapToList : (0 f : a -> b) -> (xs : LazyLst em a) -> toList (map f xs) === mapImpl f (toList xs)
  commMapToList f []        = Refl
  commMapToList f (x :: xs) = cong (f x ::) $ commMapToList f xs

public export
elemMapMaybe : {f : a -> Maybe b} -> (0 _ : IsJust $ f x) => (xs : LazyLst ne a) ->
               Elem x xs -> Elem (fromJust $ f x) $ mapMaybe f xs
elemMapMaybe (x :: _) Here with (f x)
  _ | Just _ = Here
elemMapMaybe (x :: xs) $ There y with (f x)
  _ | Just _  = There $ elemMapMaybe xs y
  _ | Nothing = elemMapMaybe xs y

public export
isJustStrengthen : {xs : LazyLst ne a} -> (0 _ : NonEmpty xs) => IsJust $ strengthen xs
isJustStrengthen {xs=_ :: _} = ItIsJust

public export
elemStrengthen : {xs : LazyLst ne a} -> (0 _ : IsJust $ strengthen xs) =>
                 Elem x xs -> Elem x $ fromJust $ strengthen xs
elemStrengthen {xs=_ :: _} p = p

public export
filterElem : {f : a -> Bool} -> {xs : LazyLst ne a} -> All (So . f) $ filter f xs
filterElem {xs=[]}      = []
filterElem {xs=x :: xs} = case @@@ f x of
  Element b prf => rewrite prf in if b
                                  then eqToSo' prf :: filterElem
                                  else filterElem
-- filterElem {xs=x :: xs} with (f x) proof prf -- No syntax for 0 prf
--   _ | False = filterElem
--   _ | True  = eqToSo prf :: filterElem
