module Syntax.WithProof.Extra

import public Data.DPair

%default total

export prefix 10 @@@

public export
(@@@) : (t : a) -> Subset a (t ===)
(@@@) t = Element t Refl
