module AgdaAsciiPrelude.AsciiPrelude where

open import Level using (Level; Lift; lift; lower) renaming (_⊔_ to _~U~_; Setω to Setw; zero to lzero; suc to lsuc) public

import Relation.Binary.PropositionalEquality as PEq
open PEq using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_; _≢_ to _=/=_) public
open PEq.≡-Reasoning using (begin_) renaming (_≡⟨⟩_ to _=<>_; step-≡ to step-=; _∎ to _qed) public

infixr 2 _=<_>_
_=<_>_ : forall {l} {A : Set l} (x {y z} : A) -> x === y -> y === z -> x === z
x =< x=y > y=z = step-= x y=z x=y

open import Function using (_$_; id; const; flip) renaming (_∘_ to _o_) public

open import Data.Product using (_,_) renaming (_×_ to _and_; proj₁ to fst; proj₂ to snd; map₁ to map1; map₂ to map2) public

infixr 2 _-x-_
_-x-_ : forall {a b} -> Set a -> Set b -> Set (a ~U~ b)
_-x-_ = _and_

open import Data.Unit.Polymorphic using (tt) renaming (⊤ to T) public
open import Data.Sum using () renaming ([_,_] to case-or; map to map-or; _⊎_ to _or_; inj₁ to left; inj₂ to right) public
open import Data.Empty using () renaming (⊥ to BOT; ⊥-elim to absurd) public
open import Relation.Nullary using (yes; no; _because_; Dec) renaming (ofʸ to of-y; ofⁿ to of-n; ¬_ to ¬_ ) public
open import Relation.Nullary.Decidable using (True; False; isYes; isNo) public

ifDec_then_else_ : forall {l l'} -> {A : Set l} -> {B : Set l'} -> Dec A -> B -> B -> B
ifDec (yes _) then a else _ = a
ifDec (no _) then _ else a = a


open import Data.Product using () renaming (Σ to Sigma; ∃ to exists) public

sigma-syntax = Sigma
infix 2 sigma-syntax
syntax sigma-syntax A (\ x -> B) = exists x of A st B

exists-syntax = exists
syntax exists-syntax (\ x -> B) = exists x st B


open import Data.List renaming (_∷_ to _::_; or to disjunct; and to conjunct; fromMaybe to maybeToList) hiding (lookup) public
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

not-involutive : forall {x} -> x === not (not x)
not-involutive {x = false} = refl
not-involutive {x = true} = refl


open import Relation.Binary using (IsDecEquivalence)
open IsDecEquivalence {{...}} using () renaming (_≟_ to _==d_) public

DecEq : forall {l} (A : Set l) -> Set _
DecEq A = IsDecEquivalence {A = A} _===_

record Eq {l} (A : Set l) : Set l where
  field
    _==_ : A -> A -> Bool
open Eq {{...}} public

_elem_ : forall {l} {A : Set l} -> {{eq : Eq A}} -> A -> List A -> Bool
x elem [] = false
x elem (y :: ys) = (x == y) || (x elem ys)

_elem_withEq_ : forall {l} {A : Set l} -> A -> List A -> Eq A -> Bool
x elem xs withEq eq = _elem_ {{eq = eq}} x xs

open import Data.Nat renaming (ℕ to Nat) public
open import Data.Nat.Instances public


open import Data.Maybe using (Maybe; just; nothing; maybe; fromMaybe; is-just; is-nothing) renaming (maybe′ to maybe'; when to whenMaybe) public

open import Data.String using (String) renaming (_++_ to _++s_; concat to concats) public
open import Data.Nat.Show using () renaming (show to showN) public

open import Category.Functor using () renaming (RawFunctor to Functor) public
open import Category.Monad using () renaming (RawMonad to Monad) public
open Monad {{...}} renaming (_⊛_ to _<*>_) hiding (zip; zipWith) public

module _ {r} (R : Set r) {a : Level} where
  open import Category.Monad.Reader R a renaming (RawMonadReader to MonadReader) public

open import Category.Monad.State renaming (RawMonadState to MonadState) public

import Data.List.Categorical as LCat
open LCat.TraversableM {{...}} public

open import Relation.Binary.Bundles public
open import Relation.Binary public

record ISTO {c l1 l2} (A : Set c) : Set (lsuc (c ~U~ l1 ~U~ l2)) where
  field
    eq : A -> A -> Set l1
    gr : A -> A -> Set l2
    overlap {{isto}} : IsStrictTotalOrder eq gr

STO-to-ISTO : forall {c l1 l2} ->
  (sto : StrictTotalOrder c l1 l2) -> let open StrictTotalOrder sto in
  ISTO {c} {l1} {l2} Carrier
STO-to-ISTO sto = record {
    eq = _ ;
    gr = _ ;
    isto = isStrictTotalOrder
  }
  where
    open StrictTotalOrder sto

STO : forall {c} {l1} {l2} ->
  (A : Set c) ->
  {{rsto : ISTO {c} {l1} {l2} A}} ->
  StrictTotalOrder c l1 l2
STO {c} {l1} {l2} A {{rsto}} = record {
  Carrier = A ;
  _≈_ = _ ;
  _<_ = _ ;
  isStrictTotalOrder = ISTO.isto rsto }

module Map {c l1 l2}
  (Key : Set c)
  {{sto : ISTO {c} {l1} {l2} Key}} where
  open import Data.Tree.AVL.Map (STO Key) renaming
    (foldr to foldrMap; initLast to initLastMap; map to mapMap) public
open Map using (Map) public
module _ {c l1 l2} {Key : Set c} {{sto : ISTO {c} {l1} {l2} Key}} where
  open Map Key {{sto}} hiding (Map) public

it : forall {l} {A : Set l} {{a : A}} -> A
it {{a}} = a
