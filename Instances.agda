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

MonadStateStateT : {{mon : Monad M}} -> MonadState S (StateT S M)
MonadStateStateT {{mon}} = StateTMonadState _ mon

MonadId : Monad {f = l} id
MonadId = record {
  return = id ; 
  _>>=_ = \a f -> f a }

MonadStateTId : Monad (StateT S id)
MonadStateTId = StateTMonad _ MonadId

MonadStateStateTId : MonadState S (StateT S id)
MonadStateStateTId = StateTMonadState _ MonadId
