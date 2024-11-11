module Data.Maybe.Properties

import public Data.Maybe
import public Control.Foldable.Elem
import public Control.Foldable.Quantifiers
import public Control.Applicative.LawfulApplicative

import Data.Pair.Properties

%hide Data.List.Quantifiers.All.All

%default total

public export %hint
lawfulFunctorMaybe : LawfulFunctor Maybe
lawfulFunctorMaybe = MkLawfulFunctor identityLaw compLaw
where
  identityLaw : (xs : Maybe a) -> xs === map Prelude.id xs
  identityLaw Nothing  = Refl
  identityLaw (Just _) = Refl

  compLaw : (xs : Maybe a) -> map g (map f xs) === map (g . f) xs
  compLaw Nothing  = Refl
  compLaw (Just _) = Refl

public export %hint
lawfulApplicativeMaybe : LawfulApplicative Maybe
lawfulApplicativeMaybe = MkLawfulApplicative
  { lawfulFunctor     = %search
  , mapApplicativeLaw = mapApplicativeLaw
  , identityApLaw     = identityApLaw
  , homomorphismLaw   = Refl
  , interchangeLaw    = interchangeLaw
  , compositionLaw    = compositionLaw
  }
where
  mapApplicativeLaw : (x : Maybe a) -> (Just f <*> x) === map f x
  mapApplicativeLaw Nothing  = Refl
  mapApplicativeLaw (Just _) = Refl

  identityApLaw : (x : Maybe a) -> (Just Prelude.id <*> x) === x
  identityApLaw Nothing  = Refl
  identityApLaw (Just _) = Refl

  interchangeLaw : (f : Maybe $ a -> b) ->
                    (f <*> Just x) === (Just ($ x) <*> f)
  interchangeLaw Nothing  = Refl
  interchangeLaw (Just _) = Refl

  compositionLaw : (f : Maybe $ b -> c) ->
                    (g : Maybe $ a -> b) ->
                    (x : Maybe a) ->
                    (Just (.) <*> f <*> g <*> x) === (f <*> (g <*> x))
  compositionLaw Nothing  _        _        = Refl
  compositionLaw (Just _) Nothing  _        = Refl
  compositionLaw (Just _) (Just _) Nothing  = Refl
  compositionLaw (Just _) (Just _) (Just _) = Refl

public export
congFromJust : forall x, y. (0 j : IsJust x) => (0 prf : x === y) ->
               fromJust @{j} x === fromJust @{replace prf j} y
congFromJust Refl = Refl

public export
isJustMap : (0 f : a -> b) -> IsJust x -> IsJust (map f x)
isJustMap _ ItIsJust = ItIsJust

public export
isJustMapInv : {x : Maybe a} -> (0 f : a -> b) -> (0 _ : IsJust $ map f x) -> IsJust x
isJustMapInv {x=Just _} _ _ = ItIsJust

public export
commMapFromJust : (0 f : a -> b) -> (x : Maybe a) -> (0 prf : IsJust x) =>
                  fromJust @{isJustMap f prf} (map f x) === f (fromJust x)
commMapFromJust _ $ Just x = Refl

public export
isJustMaybe : (0 x : Maybe a) -> (0 _ : IsJust x) => maybe e f x === f (fromJust x)
isJustMaybe _ @{ItIsJust} = Refl

isJustAp : (0 _ : IsJust f) -> (0 _ : IsJust x) -> IsJust $ f <*> x
isJustAp ItIsJust ItIsJust = ItIsJust

isJustTraverse' : {xs : List a} -> (0 _ : All (IsJust . f) xs) -> IsJust $ traverse f xs
isJustTraverse' {xs=[]     } _        = ItIsJust
isJustTraverse' {xs=_ :: xs} (h :: t) = isJustAp (isJustAp ItIsJust h) $ isJustTraverse' t

public export
isJustTraverse : Traversable t => LawfulTraversable t =>
                 (f : a -> Maybe b) -> {xs : t a} ->
                 (0 _ : All (IsJust . f) xs) -> IsJust $ traverse f xs
isJustTraverse f prf = isJustMapInv toList $ rewrite commTraverseToList f xs in isJustTraverse' prf
