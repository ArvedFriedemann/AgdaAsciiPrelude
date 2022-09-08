module AgdaAsciiPrelude.Instances where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    l l1 l2 : Level
    S : Set l
    M : Set l1 -> Set l2

decToEq : {A : Set} -> {{d : DecEq A}} -> Eq A
decToEq = record { _==_ = \x y -> Dec.does (x ==d y) }

open import Data.Maybe.Categorical

FunctorMaybe = functor

ApplicativeMaybe = applicative

MonadMaybe = monad

MonadStateT : {{mon : Monad M}} -> Monad (StateT S M)
MonadStateT {{mon}} = StateTMonad _ mon

MonadStateStateT : {{mon : Monad M}} -> MonadState S (StateT S M)
MonadStateStateT {{mon}} = StateTMonadState _ mon

MonadReaderStateT : {l1 l2 : Level} {S : Set (l1 ~U~ l2)} ->
  {M : Set (l1 ~U~ l2) -> Set (l1 ~U~ l2)} -> {{mon : Monad M}} ->
  MonadReader S {a = l2 } (StateT S M)
MonadReaderStateT {{mon}} = record {
  monad = MonadStateT ;
  reader = \ f s -> return (f s , s) ;
  local = \f m s -> m (f s) >>= \{(res , _) -> return (res , s)} }

MonadId : Monad {f = l} id
MonadId = record {
  return = id ;
  _>>=_ = \a f -> f a }

MonadStateTId : Monad (StateT S id)
MonadStateTId = StateTMonad _ MonadId

MonadStateStateTId : MonadState S (StateT S id)
MonadStateStateTId = StateTMonadState _ MonadId


eqNat : Eq Nat
eqNat = record { _==_ = _=Nat=_ }
  where
    _=Nat=_ : Nat -> Nat -> Bool
    x =Nat= y with compare x y
    ... | equal _ = true
    ... | _       = false
