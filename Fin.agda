module Fin where

open import Agda.Builtin.Nat
  using (Nat; suc)

data Fin : Nat → Set where
  zero : ∀ {n}
    → Fin (suc n)
  suc : ∀ {n} → Fin n
    → Fin (suc n)

