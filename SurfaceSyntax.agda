module SurfaceSyntax where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import BlameLabels
open import Types


data Op : Set where
  op-lam    : (pc : StaticLabel) → Type → (ℓ : StaticLabel) → Op
  op-app    : BlameLabel → Op
  op-const  : ∀ {ι} → rep ι → StaticLabel → Op
  op-if     : BlameLabel → Op
  op-ann    : Type → BlameLabel → Op
  op-let    : Type → Op
  op-ref    : StaticLabel → BlameLabel → Op
  op-deref  : Op
  op-assign : BlameLabel → Op
  -- op-input  : StaticLabel → Op

sig : Op → List Sig
sig (op-lam pc A ℓ)    = (ν ■) ∷ []
sig (op-app p)         = ■ ∷ ■ ∷ []
sig (op-const k ℓ)     = []
sig (op-if p)          = ■ ∷ ■ ∷ ■ ∷ []
sig (op-ann A p)       = ■ ∷ []
sig (op-let A)         = ■ ∷ (ν ■) ∷ []
sig (op-ref ℓ p)       = ■ ∷ []
sig op-deref           = ■ ∷ []
sig (op-assign p)      = ■ ∷ ■ ∷ []
-- sig (op-input ℓ)    = []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug; rename) public

infixl 7  _·_at_

pattern ƛ[_]_˙_of_ pc A N ℓ      = (op-lam pc A ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_at_ L M p             = (op-app p) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_of_ k ℓ                = (op-const k ℓ) ⦅ nil ⦆
pattern if_then_else_at_ L M N p = (op-if p) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern _∶_at_ M A p             = (op-ann A p) ⦅ cons (ast M) nil ⦆
pattern `let_∶_`in_ M A N        = (op-let A) ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern ref[_]_at_ ℓ M p         = (op-ref ℓ p) ⦅ cons (ast M) nil ⦆
pattern !_ M                     = op-deref ⦅ cons (ast M) nil ⦆
pattern _:=_at_ L M p            = (op-assign p) ⦅ cons (ast L) (cons (ast M) nil) ⦆
-- pattern input-of_ ℓ           = (op-input ℓ) ⦅ nil ⦆
