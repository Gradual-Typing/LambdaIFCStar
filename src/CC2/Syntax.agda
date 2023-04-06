open import Common.Types

module CC2.Syntax (Cast_⇒_ : Type → Type → Set) where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import Common.BlameLabels
open import Memory.Addr
open import CC2.Errors public


data Op : Set where
  op-addr         : (a : Addr) → (ℓ : StaticLabel) → Op
  op-lam          : (g : Label) → Type → (ℓ : StaticLabel) → Op
  op-app          : Op
  op-app?         : BlameLabel → Op
  op-app✓        : Op
  op-const        : ∀ {ι} → rep ι → StaticLabel → Op
  op-if           : Type → Op
  op-if⋆          : Type → Op
  op-let          : Op
  op-ref          : StaticLabel → Op
  op-ref?         : StaticLabel → BlameLabel → Op
  op-ref✓        : StaticLabel → Op
  op-deref        : Op
  op-assign       : Op
  op-assign?      : BlameLabel → Op
  op-assign✓     : Op
  op-cast         : ∀ {A B} → Cast A ⇒ B → Op
  op-prot         : Label → StaticLabel → Op
  op-blame        : Error → BlameLabel → Op
  {- Terms that only appear in erasure -}
  op-opaque       : Op

sig : Op → List Sig
sig (op-addr a ℓ)      = []
sig (op-lam g A ℓ)     = (ν ■) ∷ []
sig op-app             = ■ ∷ ■ ∷ []
sig (op-app? p)        = ■ ∷ ■ ∷ []
sig op-app✓           = ■ ∷ ■ ∷ []
sig (op-const k ℓ)     = []
sig (op-if A)          = ■ ∷ ■ ∷ ■ ∷ []
sig (op-if⋆ A)         = ■ ∷ ■ ∷ ■ ∷ []
sig op-let             = ■ ∷ (ν ■) ∷ []
sig (op-ref  ℓ)        = ■ ∷ []
sig (op-ref? ℓ p)      = ■ ∷ []
sig (op-ref✓ ℓ)       = ■ ∷ []
sig op-deref           = ■ ∷ []
sig op-assign          = ■ ∷ ■ ∷ []
sig (op-assign? p)     = ■ ∷ ■ ∷ []
sig op-assign✓        = ■ ∷ ■ ∷ []
sig (op-cast c)        = ■ ∷ []
sig (op-prot g ℓ)      = ■ ∷ []
sig (op-blame e p)     = []
sig op-opaque          = []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infix 8 _⟨_⟩

pattern addr_of_ a ℓ             = (op-addr a ℓ) ⦅ nil ⦆
pattern ƛ_,_˙_of_ g A N ℓ        = (op-lam g A ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern app L M                  = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern app? L M p               = (op-app? p) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern app✓ L M                = op-app✓ ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_of_ k ℓ                = (op-const k ℓ) ⦅ nil ⦆
pattern if L A M N               = (op-if A) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern if⋆ L A M N              = (op-if⋆ A) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern `let M N                 = op-let ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern ref⟦_⟧ ℓ M               = (op-ref ℓ) ⦅ cons (ast M) nil ⦆
pattern ref?⟦_⟧ ℓ M p            = (op-ref? ℓ p) ⦅ cons (ast M) nil ⦆
pattern ref✓⟦_⟧ ℓ M             = (op-ref✓ ℓ) ⦅ cons (ast M) nil ⦆
pattern !_ M                     = op-deref ⦅ cons (ast M) nil ⦆
pattern assign  L M              = op-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern assign? L M p            = (op-assign? p) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern assign✓ L M             = op-assign✓ ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⟨_⟩ M c                 = (op-cast c) ⦅ cons (ast M) nil ⦆
pattern prot g ℓ M               = (op-prot g ℓ) ⦅ cons (ast M) nil ⦆    {- protection term -}
pattern blame e p                = (op-blame e p) ⦅ nil ⦆                {- cast or NSU errors -}
pattern ●                       = op-opaque ⦅ nil ⦆                     {- opaque value -}
