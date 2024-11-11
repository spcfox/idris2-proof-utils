module Data.List.Elem.Properties

import public Data.List
import public Data.List.Elem

%default total

public export
nonEmptyElem : {0 x : a} -> {xs : List a} -> (0 _ : Elem x xs) -> NonEmpty xs
nonEmptyElem {xs=_ ::_} _ = IsNonEmpty

public export
inverseMap : (0 f : a -> b) -> (xs : List a) -> Elem x (map f xs) -> (y ** (Elem y xs, f y = x))
inverseMap f (y :: _)  $ Here    = (y ** (Here, Refl))
inverseMap f (_ :: xs) $ There z = let (y ** (e, p)) = inverseMap f xs z in (y ** (There e, p))
