module Control.Relation.Interchange

import public Control.Relation
import public Control.WellFounded

%default total

data InterachangeRel : Rel a -> Rel b -> Rel (a, b) where
  LeftRel  : forall x. x `relA` x' -> InterachangeRel relA relB (x, y) (x', y)
  RightRel : forall y. y `relB` y' -> InterachangeRel relA relB (x, y) (x, y')

WellFounded a relA => WellFounded b relB => WellFounded (a, b) (InterachangeRel relA relB) where
  wellFounded (x, y) = helper x y
  where
    helper : (x : a) -> (y : b) -> Accessible (InterachangeRel relA relB) (x, y)
    helper =
      wfInd $ \_, accX =>
        wfInd $ \y, accY =>
          Access $ \(x', y') => \case
            LeftRel  r => accX x' r y
            RightRel r => accY y' r
