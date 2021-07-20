module AgdaAsciiPrelude.AsciiPrelude where

open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to _~U~_; Setω to Setw) public

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_; _≢_ to _=/=) public
open Eq.≡-Reasoning using (begin_) renaming (_≡⟨⟩_ to _=<>_; step-≡ to step-=; _∎ to _qed) public

infixr 2 _=<_>_
_=<_>_ : forall {l} {A : Set l} (x {y z} : A) -> x === y -> y === z -> x === z
x =< x=y > y=z = step-= x y=z x=y

open import Function using (_$_) renaming (_∘_ to _o_) public

open import Data.Product using (_,_) renaming (_×_ to _and_; proj₁ to fst; proj₂ to snd) public

_-x-_ : forall {a b} -> Set a -> Set b -> Set (a ~U~ b)
_-x-_ = _and_

open import Data.Unit using () renaming (⊤ to T; tt to top) public
open import Data.Sum using () renaming ([_,_] to case-or; _⊎_ to _or_; inj₁ to left; inj₂ to right) public
open import Data.Empty using () renaming (⊥ to BOT; ⊥-elim to absurd) public
open import Relation.Nullary using (yes; no; _because_; Dec) renaming (ofʸ to of-y; ofⁿ to of-n; ¬_ to ¬_ ) public
open import Relation.Nullary.Decidable using (True; False)

record DecEq {l} (A : Set l) : Set l where
  infixr 4 _==_
  field
    _==_ : (a1 : A) -> (a2 : A) -> Dec (a1 === a2)
open DecEq {{...}} public

ifDec_then_else_ : forall {l l'} -> {A : Set l} -> {B : Set l'} -> Dec A -> B -> B -> B
ifDec (yes _) then a else _ = a
ifDec (no _) then _ else a = a


open import Data.Product using () renaming (Σ to sigma; ∃ to exists) public

sigma-syntax = sigma
infix 2 sigma-syntax
syntax sigma-syntax A (\ x -> B) = exists x of A st B

exists-syntax = exists
syntax exists-syntax (\ x -> B) = exists x st B


open import Data.List renaming (_∷_ to _::_; or to disjunct; and to conjunct) public
open import Data.Bool using (Bool; true; false; not; _xor_; if_then_else_) renaming (_∧_ to _&&_; _∨_ to _||_; T to Tt) public

double-not : {x y : Bool} -> x === (not $ not y) -> x === y
double-not {x} {false} x=¬¬y = x=¬¬y
double-not {x} {true} x=¬¬y = x=¬¬y

double-not' : {x y : Bool} -> x === y -> x === (not $ not y)
double-not' {x} {false} x=y = x=y
double-not' {x} {true} x=y = x=y

and-false : {x y : Bool} -> x && y === false -> (x === false) or (y === false)
and-false {false} {y} x&&y=f = left refl
and-false {true} {false} x&&y=f = right refl

and-true : {x y : Bool} -> x && y === true -> (x === true) and (y === true)
and-true {true} {true} x&&y=f = refl , refl

or-true : {x y : Bool} -> x || y === true -> (x === true) or (y === true)
or-true {true} {y} x&&y=f = left refl
or-true {false} {true} x&&y=f = right refl

or-false : {x y : Bool} -> x || y === false -> (x === false) and (y === false)
or-false {false} {false} x&&y=f = refl , refl


open import Data.Nat renaming (ℕ to Nat) public

--
