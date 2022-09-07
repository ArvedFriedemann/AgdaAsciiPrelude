module AgdaAsciiPrelude.Instances where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    l l1 l2 : Level
    S : Set l
    M : Set l1 -> Set l2

decToEq : {A : Set} -> {{d : DecEq A}} -> Eq A
decToEq = record { _==_ = \x y -> Dec.does (x ==d y) }

open import Data.Maybe.Instances

FunctorMaybe = maybeFunctor

ApplicativeMaybe = maybeApplicative

MonadMaybe = maybeMonad

MonadStateT : {{mon : Monad M}} -> Monad (StateT S M)
MonadStateT {{mon}} = StateTMonad _ mon
