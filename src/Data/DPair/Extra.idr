module Data.DPair.Extra

import public Data.DPair

%default total

namespace DPair

  public export
  mapSnd : forall b, c. (forall x. b x -> c x) -> (x : a ** b x) -> (x : a ** c x)
  mapSnd = bimap id

namespace Exists

  public export
  mapSnd : forall b, c. (forall x. b x -> c x) -> Exists b -> Exists c
  mapSnd = bimap id

namespace Subset

  public export
  mapSnd : forall b, c. (0 _ : forall x. b x -> c x) -> Subset a b -> Subset a c
  mapSnd = bimap id
