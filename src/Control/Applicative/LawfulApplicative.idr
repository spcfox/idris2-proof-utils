module Control.Applicative.LawfulApplicative

import public Control.Functor.LawfulFunctor

import Syntax.PreorderReasoning

%default total

public export
record LawfulApplicative t {auto 0 applicative : Applicative t} where
  [search applicative]
  constructor MkLawfulApplicative

  lawfulFunctor : LawfulFunctor t

  mapApplicativeLaw : forall a, b. {0 f : a -> b} ->
                      (x : t a) -> (pure f <*> x) === map f x

  identityApLaw : forall a. (x : t a) -> (pure Prelude.id <*> x) === x

  homomorphismLaw : forall a, b. {0 f : a -> b} -> {0 x : a} ->
                    (pure f <*> pure x) {f=t} === pure (f x)

  interchangeLaw : forall a, b. {0 x : a} -> (f : t $ a -> b) ->
                   f <*> pure x = pure ($ x) <*> f

  compositionLaw : forall a, b, c. (f : t $ b -> c) -> (g : t $ a -> b) -> (x : t a) ->
                   (pure (.) <*> f <*> g <*> x) === (f <*> (g <*> x))

public export %hint
lawfulFunctor : (0 _ : Applicative t) => LawfulApplicative t => LawfulFunctor t
lawfulFunctor = %search.lawfulFunctor

public export
mapApplicativeLaw : (0 _ : Applicative t) => LawfulApplicative t =>
                    (x : t a) -> (pure f <*> x) === map f x
mapApplicativeLaw = %search.mapApplicativeLaw

public export
identityApLaw : (0 _ : Applicative t) => LawfulApplicative t =>
                (x : t a) -> (pure Prelude.id <*> x) === x
identityApLaw = %search.identityApLaw

public export
homomorphismLaw : (0 _ : Applicative t) => LawfulApplicative t =>
                  (pure f <*> pure x) {f=t} === pure (f x)
homomorphismLaw = %search.homomorphismLaw

public export
interchangeLaw : (0 _ : Applicative t) => LawfulApplicative t =>
                 (f : t $ a -> b) -> f <*> pure x = pure ($ x) <*> f
interchangeLaw = %search.interchangeLaw

public export
compositionLaw : (0 _ : Applicative t) => LawfulApplicative t =>
                 (f : t $ b -> c) -> (g : t $ a -> b) -> (x : t a) ->
                 (pure (.) <*> f <*> g <*> x) === (f <*> (g <*> x))
compositionLaw = %search.compositionLaw

public export
interchange2Law : (0 _ : Applicative t) => LawfulApplicative t =>
                  (x : t a) -> (pure f <*> x <*> pure y) === (pure (flip f y) <*> x)
interchange2Law x =
  Calc $
    |~ pure f <*> x <*> pure y
    ~~ pure ($ y) <*> (pure f <*> x)
      ...( interchangeLaw _ )
    ~~ pure (.) <*> pure ($ y) <*> pure f <*> x
      ...( sym $ compositionLaw _ _ _ )
    ~~ pure (($ y) .) <*> pure f <*> x
      ...( cong (<*> pure f <*> x) $ homomorphismLaw )
    ~~ pure (flip f y) <*> x
      ...( cong (<*> x) $ homomorphismLaw )
