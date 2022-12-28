module Memory.Addr where

open import Data.Nat using (ℕ)

open import Common.SecurityLabels using (StaticLabel)


RawAddr = ℕ

data Addr : Set where
  a⟦_⟧_ : StaticLabel → RawAddr → Addr
