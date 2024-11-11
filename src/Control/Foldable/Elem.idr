module Control.Foldable.Elem

import public Data.List
import public Data.List.Elem
import Data.List.Elem.Properties

import Data.List.Elem.Properties
import Control.Functor.LawfulFoldableFunctor

%default total

public export
Elem : Foldable t => a -> t a -> Type
Elem a = List.Elem.Elem a . toList

%hide List.Elem.Elem

public export
NonEmpty : Foldable t => t a -> Type
NonEmpty = Data.List.NonEmpty . toList

public export
elemMap : (0 _ : Functor t) => (0 _ : Foldable t) => LawfulFoldableFunctor t =>
          (0 f : a -> b) -> {0 x : a} -> {xs : t a} -> Elem x xs -> Elem (f x) $ map f xs
elemMap f prf = rewrite commMapToList f xs in elemMap f prf

public export
inverseMap : (0 _ : Functor t) => (_ : Foldable t) => LawfulFoldableFunctor t =>
             (0 f : a -> b) -> (xs : t a) -> Elem x (map f xs) -> (y ** (Elem y xs, f y = x))
inverseMap f xs e = inverseMap f _ $ rewrite sym $ commMapToList f xs in e
