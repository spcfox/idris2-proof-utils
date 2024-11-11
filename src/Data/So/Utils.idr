module Data.So.Utils

import Control.Relation
import public Data.DPair
import Data.DPair.Extra
import public Data.So
import Syntax.WithProof.Extra

%default total

public export %inline
eqToSo' : (0 _ : b = True) -> So b
eqToSo' Refl = Oh

public export
BoolWithProof : Bool -> Bool -> Type
BoolWithProof b True  = So b
BoolWithProof b False = So $ not b

public export
Reflexive Bool BoolWithProof where
  reflexive = if x then Oh else Oh

public export
boolWithProof : (b : Bool) -> Subset Bool $ BoolWithProof b
boolWithProof b = mapSnd (\Refl => reflexive {rel=BoolWithProof}) $ @@@ b
