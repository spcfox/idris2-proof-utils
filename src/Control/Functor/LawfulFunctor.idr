module Control.Functor.LawfulFunctor

%default total

public export
record LawfulFunctor t {auto 0 functor : Functor t} where
  [search functor]
  constructor MkLawfulFunctor

  identityLaw : forall a. (xs : t a) -> xs === map Prelude.id xs

  compLaw : forall a, b, c. {0 g : b -> c} -> {0 f : a -> b} ->
            (xs : t a) -> map g (map f xs) === map (g . f) xs

public export
identityLaw : (0 _ : Functor t) => LawfulFunctor t => (xs : t a) -> xs === map Prelude.id xs
identityLaw = %search.identityLaw

public export
compLaw : (0 _ : Functor t) => LawfulFunctor t =>
          (xs : t a) -> map g (map f xs) === map (g . f) xs
compLaw = %search.compLaw
