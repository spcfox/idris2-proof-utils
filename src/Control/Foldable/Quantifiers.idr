module Control.Foldable.Quantifiers

import public Data.List.Quantifiers

import public Control.Foldable.Elem
import Data.List.Properties
import Data.List.Quantifiers.Properties

%default total

public export
All : Foldable t => (0 p : a -> Type) -> t a -> Type
All p = List.Quantifiers.All.All p . toList

%hide List.Quantifiers.All.All

public export
allMapForall : (0 _ : Functor t) => Foldable t => LawfulFoldableFunctor t =>
               {0 f : a -> b} -> {xs : t a} -> ({x : a} -> (0 _ : Elem x xs) -> p (f x)) -> All p $ map f xs
allMapForall h = rewrite commMapToList f xs in allMapForall h

-- public export
-- allElem : (0 _ : Functor t) => Foldable t =>
--           {xs : t a} -> ({x : a} -> (0 _ : Elem x xs) -> p x) -> All p xs
-- allElem = allElem

-- public export
-- allTrue : (0 _ : Functor t) => Foldable t =>
--           {xs : t a} -> ({x : a} -> p x) -> All p xs
-- allTrue = allTrue

public export
allMap : (0 _ : Functor t) => (0 _ : Foldable t) => LawfulFoldableFunctor t =>
         {0 f : a -> b} -> {0 xs : t a} -> All (p . f) xs -> All p $ map f xs
allMap h = rewrite commMapToList f xs in allMap h

public export
allMapInv : (0 _ : Functor t) => Foldable t => LawfulFoldableFunctor t =>
            {0 f : a -> b} -> {xs : t a} -> All p (map f xs) -> All (p . f) xs
allMapInv = rewrite commMapToList f xs in allMapInv
