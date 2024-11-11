module Control.Relation.TransitiveClojure

import public Control.Relation
import public Control.WellFounded

%default total

data TransitiveClosure : Rel ty -> ty -> ty -> Type where
  Base : forall x, y. rel x y -> TransitiveClosure rel x y
  Step : forall x, z. {y : ty} -> rel x y -> TransitiveClosure rel y z -> TransitiveClosure rel x z

Cast (Accessible rel x) (Accessible (TransitiveClosure rel) x) where
  cast $ Access acc = Access helper
  where
    helper : (y : _) -> TransitiveClosure rel y x -> Accessible (TransitiveClosure rel) y
    helper y $ Base r    = cast $ acc y r
    helper y $ Step r rs = case helper _ rs of (Access acc) => acc _ $ Base r

-- WellFounded a rel => WellFounded a (TransitiveClosure rel) where
--   wellFounded x = cast $ wellFounded {rel} x

Cast (Accessible (TransitiveClosure rel) x) (Accessible rel x) where
  cast $ Access acc = Access $ \y => cast . acc y . Base

-- TODO: very slow typecheck
-- (wf : WellFounded a (TransitiveClosure rel)) => WellFounded a rel where
{wf : WellFounded a $ TransitiveClosure rel} -> WellFounded a rel where
  wellFounded x = cast $ wellFounded @{wf} {rel=TransitiveClosure rel} x
