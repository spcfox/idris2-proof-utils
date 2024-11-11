module Data.List.Quantifiers.Properties

import public Data.List.Quantifiers

import Data.List.Elem
import Data.List.Properties

%default total

public export
allMapForall : {0 f : a -> b} -> {xs : List a} -> ({x : a} -> (0 _ : Elem x xs) -> p (f x)) -> All p $ map f xs
allMapForall {xs=[]}      _ = []
allMapForall {xs=x :: xs} h = h Here :: allMapForall (\e => h $ There e)

public export
allElem : {xs : List a} -> ({x : a} -> (0 _ : Elem x xs) -> p x) -> All p xs
allElem h = rewrite identityLaw {xs} in allMapForall h

public export
allTrue : {xs : List a} -> ({x : a} -> p x) -> All p xs
allTrue h = allElem $ \_ => h

public export
allMap : {0 f : a -> b} -> All (p . f) xs -> All p $ map f xs
allMap $ []      = []
allMap $ h :: hs = h :: allMap hs

public export
allMapInv : {0 f : a -> b} -> {xs : List a} -> All p (map f xs) -> All (p . f) xs
allMapInv {xs=[]}     $ []      = []
allMapInv {xs=_ :: _} $ h :: hs = h :: allMapInv hs
