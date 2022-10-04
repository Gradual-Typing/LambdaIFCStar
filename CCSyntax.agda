open import Types

module CCSyntax (Cast_⇒_ : Type → Type → Set) where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import BlameLabels
open import Addr


data Error : Set where
  blame     : BlameLabel → Error
  nsu-error : Error

data Op : Set where
  op-addr         : (a : Addr) → (ℓ : StaticLabel) → Op
  op-lam          : (pc : StaticLabel) → Type → (ℓ : StaticLabel) → Op
  op-app          : Op
  op-const        : ∀ {ι} → rep ι → StaticLabel → Op
  op-if           : Type → Op
  op-let          : Op
  op-ref          : StaticLabel → Op
  op-ref?         : StaticLabel → Op
  op-ref✓         : StaticLabel → Op
  op-deref        : Op
  op-assign       : Op
  op-assign?      : Op
  op-assign✓      : Op
  op-cast         : ∀ {A B} → Cast A ⇒ B → Op
  op-prot         : StaticLabel → Op
  op-cast-pc      : Label → Op
  op-error        : Error → Op
  {- Terms that only appear in erasure -}
  op-opaque       : Op
  -- op-discard      : Op

sig : Op → List Sig
sig (op-addr a ℓ)      = []
sig (op-lam pc A ℓ)    = (ν ■) ∷ []
sig op-app             = ■ ∷ ■ ∷ []
sig (op-const k ℓ)     = []
sig (op-if A)          = ■ ∷ ■ ∷ ■ ∷ []
sig op-let             = ■ ∷ (ν ■) ∷ []
sig (op-ref  ℓ)        = ■ ∷ []
sig (op-ref? ℓ)        = ■ ∷ []
sig (op-ref✓ ℓ)        = ■ ∷ []
sig op-deref           = ■ ∷ []
sig op-assign          = ■ ∷ ■ ∷ []
sig op-assign?         = ■ ∷ ■ ∷ []
sig op-assign✓         = ■ ∷ ■ ∷ []
sig (op-cast c)        = ■ ∷ []
sig (op-prot ℓ)        = ■ ∷ []
sig (op-cast-pc g)     = ■ ∷ []
sig (op-error e)       = []
sig op-opaque          = []
-- sig op-discard         = ■ ∷ []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infixl 7  _·_
infix 8 _⟨_⟩

pattern addr_of_ a ℓ             = (op-addr a ℓ) ⦅ nil ⦆
pattern ƛ[_]_˙_of_ pc A N ℓ      = (op-lam pc A ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M                  = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_of_ k ℓ                = (op-const k ℓ) ⦅ nil ⦆
pattern if L A M N               = (op-if A) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern `let M N                 = op-let ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern ref[_]_  ℓ M             = (op-ref ℓ) ⦅ cons (ast M) nil ⦆
pattern ref?[_]_ ℓ M             = (op-ref? ℓ) ⦅ cons (ast M) nil ⦆
pattern ref✓[_]_ ℓ M             = (op-ref✓ ℓ) ⦅ cons (ast M) nil ⦆
pattern !_ M                     = op-deref ⦅ cons (ast M) nil ⦆
pattern _:=_  L M                = op-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _:=?_ L M                = op-assign? ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _:=✓_ L M                = op-assign✓ ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⟨_⟩ M c                 = (op-cast c) ⦅ cons (ast M) nil ⦆
pattern prot ℓ M                 = (op-prot ℓ) ⦅ cons (ast M) nil ⦆      {- protection term -}
pattern cast-pc g M              = (op-cast-pc g) ⦅ cons (ast M) nil ⦆
pattern error e                  = (op-error e) ⦅ nil ⦆                  {- blame / nsu error -}
-- pattern discard M                = op-discard ⦅ cons (ast M) nil ⦆       {- discarding value as ● -}
pattern ●                        = op-opaque ⦅ nil ⦆                     {- opaque value -}
