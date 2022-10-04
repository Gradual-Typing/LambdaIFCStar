module HeapContext where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Types
open import Addr public

HalfHeapContext = List (RawAddr × RawType)
HeapContext     = HalfHeapContext × HalfHeapContext

lookup-Σ : HeapContext → Addr → Maybe RawType
lookup-Σ ⟨ Σᴸ , Σᴴ ⟩ (a[ low  ] n) = find _≟_ Σᴸ n
lookup-Σ ⟨ Σᴸ , Σᴴ ⟩ (a[ high ] n) = find _≟_ Σᴴ n


infix 4 _⊇_

_⊇_ : ∀ (Σ′ Σ : HeapContext) → Set
Σ′ ⊇ Σ = ∀ a {T} → lookup-Σ Σ a ≡ just T → lookup-Σ Σ′ a ≡ just T

⊇-refl : ∀ Σ → Σ ⊇ Σ
⊇-refl Σ a eq = eq

⊇-trans : ∀ {Σ₁ Σ₂ Σ₃} → Σ₁ ⊇ Σ₂ → Σ₂ ⊇ Σ₃ → Σ₁ ⊇ Σ₃
⊇-trans Σ₁⊇Σ₂ Σ₂⊇Σ₃ a eq = Σ₁⊇Σ₂ a (Σ₂⊇Σ₃ a eq)

cons-Σ : Addr → RawType → HeapContext → HeapContext
cons-Σ (a[ low  ] n) T ⟨ Σᴸ , Σᴴ ⟩ = ⟨ ⟨ n , T ⟩ ∷ Σᴸ , Σᴴ ⟩
cons-Σ (a[ high ] n) T ⟨ Σᴸ , Σᴴ ⟩ = ⟨ Σᴸ , ⟨ n , T ⟩ ∷ Σᴴ ⟩

lookup-Σ-cons : ∀ a {T} Σ
  → lookup-Σ (cons-Σ a T Σ) a ≡ just T
lookup-Σ-cons (a[ high ] n) ⟨ Σᴸ , Σᴴ ⟩ with n ≟ n
... | yes refl = refl
... | no  n≢n  = contradiction refl n≢n
lookup-Σ-cons (a[ low ] n) ⟨ Σᴸ , Σᴴ ⟩ with n ≟ n
... | yes refl = refl
... | no  n≢n  = contradiction refl n≢n
