{- Precision relation of CC2 -}

open import Common.Types

module CC2.Precision where

open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Common.Utils
open import Common.Types
open import Common.Coercions
open import Memory.HeapContext
open import CC2.Syntax


infix 4 _;_∣_;_∣_;_∣_;_⊢_⊑_⇐_⊑_

data _;_∣_;_∣_;_∣_;_⊢_⊑_⇐_⊑_ : (Γ Γ′ : Context) (Σ Σ′ : HeapContext)
  (g g′ : Label) (ℓ ℓ′ : StaticLabel) (M M′ : Term) (A A′ : Type) → Set where

  ⊑-var : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ x}
    → Γ  ∋ x ⦂ A
    → Γ′ ∋ x ⦂ A′
      ---------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ` x ⊑ ` x ⇐ A ⊑ A′
