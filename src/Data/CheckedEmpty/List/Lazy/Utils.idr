module Data.CheckedEmpty.List.Lazy.Utils

import Data.CheckedEmpty.List.Lazy

import Control.Foldable.Elem

%default total

public export
mapElem : (xs : LazyLst ne a) -> ((x : a) -> (0 _ : Elem x xs) -> b) -> LazyLst ne b
mapElem []        _ = []
mapElem (x :: xs) f = f x Here :: mapElem xs (\y, e => f y $ There e)
