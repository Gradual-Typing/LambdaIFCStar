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
  op-lam          : (g : Label) → Type → Type → (ℓ : StaticLabel) → Op
  op-app          : (ℓᶜ : StaticLabel) → Type → Type → (ℓ : StaticLabel) → Op
  op-app?         : Type → Type → BlameLabel → Op
  op-app✓        : (ℓᶜ : StaticLabel) → Type → Type → (ℓ : StaticLabel) → Op
  op-const        : ∀ {ι} → rep ι → StaticLabel → Op
  op-if           : Type → (ℓ : StaticLabel) → Op
  op-if⋆          : Type → Op
  op-let          : Type → Op
  op-ref          : StaticLabel → RawType → Op
  op-ref?         : StaticLabel → RawType → BlameLabel → Op
  op-ref✓        : StaticLabel → RawType → Op
  op-deref        : Type → Label → Op
  op-assign       : RawType → StaticLabel → StaticLabel → Op
  op-assign?      : RawType → BlameLabel → Op
  op-assign✓     : RawType → StaticLabel → StaticLabel → Op
  op-cast         : ∀ {A B} → Cast A ⇒ B → Op
  op-prot         : Label → StaticLabel → Type → Op
  op-blame        : Error → BlameLabel → Op
  {- Terms that only appear in erasure -}
  op-opaque       : Op

sig : Op → List Sig
sig (op-addr a ℓ)      = []
sig (op-lam g A B ℓ)   = (ν ■) ∷ []
sig (op-app ℓᶜ A B ℓ)  = ■ ∷ ■ ∷ []
sig (op-app? A B p)    = ■ ∷ ■ ∷ []
sig (op-app✓ ℓᶜ A B ℓ) = ■ ∷ ■ ∷ []
sig (op-const k ℓ)     = []
sig (op-if A ℓ)        = ■ ∷ ■ ∷ ■ ∷ []
sig (op-if⋆ A)         = ■ ∷ ■ ∷ ■ ∷ []
sig (op-let A)         = ■ ∷ (ν ■) ∷ []
sig (op-ref ℓ T)       = ■ ∷ []
sig (op-ref? ℓ T p)    = ■ ∷ []
sig (op-ref✓ ℓ T)     = ■ ∷ []
sig (op-deref A g)     = ■ ∷ []
sig (op-assign T ℓ̂ ℓ)  = ■ ∷ ■ ∷ []
sig (op-assign? T p)   = ■ ∷ ■ ∷ []
sig (op-assign✓ T ℓ̂ ℓ) = ■ ∷ ■ ∷ []
sig (op-cast c)        = ■ ∷ []
sig (op-prot g ℓ A)    = ■ ∷ []
sig (op-blame e p)     = []
sig op-opaque          = []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infix 8 _⟨_⟩

pattern addr_of_ a ℓ             = (op-addr a ℓ) ⦅ nil ⦆
pattern ƛ_˙_∶_⇒_of_ g N A B ℓ   = (op-lam g A B ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern app L M ℓᶜ A B ℓ         = (op-app ℓᶜ A B ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern app? L M A B p           = (op-app? A B p) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern app✓ L M ℓᶜ A B ℓ       = (op-app✓ ℓᶜ A B ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_of_ k ℓ                = (op-const k ℓ) ⦅ nil ⦆
pattern if L A ℓ M N             = (op-if A ℓ) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern if⋆ L A M N              = (op-if⋆ A) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern `let M A N               = (op-let A) ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern ref⟦_⟧ ℓ T M             = (op-ref ℓ T) ⦅ cons (ast M) nil ⦆
pattern ref?⟦_⟧ ℓ T M p          = (op-ref? ℓ T p) ⦅ cons (ast M) nil ⦆
pattern ref✓⟦_⟧ ℓ T M           = (op-ref✓ ℓ T) ⦅ cons (ast M) nil ⦆
pattern ! M A g                  = (op-deref A g) ⦅ cons (ast M) nil ⦆
pattern assign L M T ℓ̂ ℓ         = (op-assign T ℓ̂ ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern assign? L M T p          = (op-assign? T p) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern assign✓ L M T ℓ̂ ℓ       = (op-assign✓ T ℓ̂ ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⟨_⟩ M c                 = (op-cast c) ⦅ cons (ast M) nil ⦆
pattern prot g ℓ A M             = (op-prot g ℓ A) ⦅ cons (ast M) nil ⦆    {- protection term -}
pattern blame e p                = (op-blame e p) ⦅ nil ⦆                {- cast or NSU errors -}
pattern ●                       = op-opaque ⦅ nil ⦆                     {- opaque value -}
