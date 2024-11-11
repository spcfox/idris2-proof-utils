module Data.List.Utils

import Data.List.Elem

%default total

public export
mapElem : (xs : List a) -> ((x : a) -> (0 _ : Elem x xs) -> b) -> List b
mapElem []        _ = []
mapElem (x :: xs) f = f x Here :: mapElem xs (\y, e => f y $ There e)
