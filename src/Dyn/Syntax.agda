module Dyn.Syntax where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Common.SecurityLabels
open import Common.Types using (Base; rep)
open import Syntax
open import Memory.Addr


data Op : Set where
  op-const        : ∀ {ι} → rep ι → StaticLabel → Op
  op-addr         : (a : Addr) → (ℓ : StaticLabel) → Op
  op-lam          : (ℓ : StaticLabel) → Op
  op-app          : Op
  op-if           : Op
  op-ref?         : StaticLabel → Op
  op-deref        : Op
  op-assign?      : Op
  -- op-error        : Op
  op-prot         : StaticLabel → Op   -- only in small-step
  op-opaque       : Op                  -- only in erasure


sig : Op → List Sig
sig (op-const k ℓ)     = []
sig (op-addr a ℓ)      = []
sig (op-lam ℓ)         = (ν ■) ∷ []
sig op-app             = ■ ∷ ■ ∷ []
sig op-if              = ■ ∷ ■ ∷ ■ ∷ []
sig (op-ref? ℓ)        = ■ ∷ []
sig op-deref           = ■ ∷ []
sig op-assign?         = ■ ∷ ■ ∷ []
-- sig op-error           = []
sig (op-prot ℓ)        = ■ ∷ []
sig op-opaque          = []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infixl 7  _·_

pattern $_of_ k ℓ                = (op-const k ℓ) ⦅ nil ⦆
pattern addr_of_ a ℓ             = (op-addr a ℓ) ⦅ nil ⦆
pattern ƛ_of_ N ℓ                = (op-lam ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M                  = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern if L M N                 = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern ref?⟦_⟧_ ℓ M             = (op-ref? ℓ) ⦅ cons (ast M) nil ⦆
pattern !_ M                     = op-deref ⦅ cons (ast M) nil ⦆
pattern _:=?_ L M                = op-assign? ⦅ cons (ast L) (cons (ast M) nil) ⦆
-- pattern error                    = op-error ⦅ nil ⦆
pattern prot ℓ M                 = (op-prot ℓ) ⦅ cons (ast M) nil ⦆
pattern ●                       = op-opaque ⦅ nil ⦆            {- opaque value -}
