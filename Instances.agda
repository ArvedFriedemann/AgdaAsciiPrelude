module AgdaAsciiPrelude.Instances where

open import AgdaAsciiPrelude.AsciiPrelude

decToEq : {A : Set} -> {{d : DecEq A}} -> Eq A
decToEq = record { _==_ = \x y -> Dec.does (x ==d y) }
