module AgdaAsciiPrelude.TrustMe where

open import AgdaAsciiPrelude.AsciiPrelude
open import Agda.Builtin.TrustMe

private
  variable
    A B : Set

trustVal : (a : A) -> B
trustVal {A} {B} a with primTrustMe {x = A} {y = B}
... | refl = a

postulate dummy : {A : Set} -> A
