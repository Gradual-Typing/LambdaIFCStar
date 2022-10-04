module Addr where

open import Data.Nat using (ℕ)
open import SecurityLabels using (StaticLabel)

RawAddr = ℕ

data Addr : Set where
  a[_]_ : StaticLabel → RawAddr → Addr
