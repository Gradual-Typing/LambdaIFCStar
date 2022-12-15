{- Precision relation of the cast calculus -}

open import Types

module CCPrecision where

open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import HeapContext
open import TypeBasedCast
open import CC

{- M ⊑ M′ always implies A ⊑ A′ if ⊢ M ⦂ A and ⊢ M′ ⦂ A′ -}
infix 4 _⊑_⊢_

data _⊑_⊢_ : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ M M′}
  → Γ  ; Σ  ; gc  ; pc  ⊢ M  ⦂ A
  → Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
  → A ⊑ A′ → Set where

  ⊑-var : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ x}
    → (Γ∋x : Γ ∋ x ⦂ A)
    → (Γ′∋x : Γ′ ∋ x ⦂ A′)
    → (A⊑A′ : A ⊑ A′)
      ----------------------------------------------------------------------
    → ⊢var {Γ} {Σ} {gc} {pc} Γ∋x ⊑ ⊢var {Γ′} {Σ′} {gc′} {pc′} Γ′∋x ⊢ A⊑A′

  ⊑-const : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {ι} {k : rep ι} {ℓ}
      ----------------------------------------------------------------------
    → ⊢const {Γ} {Σ} {gc} {pc} {ι} {k} ⊑ ⊢const {Γ′} {Σ′} {gc′} {pc′} {ι} {k} ⊢ (⊑-ty (l⊑l {ℓ}) ⊑-ι)

  ⊑-addr : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {T T′} {n ℓ ℓ̂}
    → (Σ[a]≡T   : lookup-Σ Σ  (a⟦ ℓ̂ ⟧ n) ≡ just T )
    → (Σ′[a]≡T′ : lookup-Σ Σ′ (a⟦ ℓ̂ ⟧ n) ≡ just T′)
    → (T⊑T′ : T ⊑ᵣ T′)
      ----------------------------------------------------------------------
    → ⊢addr {Γ} {Σ} {gc} {pc} Σ[a]≡T ⊑ ⊢addr {Γ′} {Σ′} {gc′} {pc′} Σ′[a]≡T′ ⊢ ⊑-ty (l⊑l {ℓ}) (⊑-ref (⊑-ty (l⊑l {ℓ̂}) T⊑T′))

  ⊑-lam : ∀ {Γ Γ′ Σ Σ′ gc gc′ pc pc′} {A A′ B B′ N N′} {ℓᶜ ℓ}
    → (⊢N  : ∀ {pc} → A  ∷ Γ  ; Σ  ; l ℓᶜ ; pc ⊢ N  ⦂ B )
    → (⊢N′ : ∀ {pc} → A′ ∷ Γ′ ; Σ′ ; l ℓᶜ ; pc ⊢ N′ ⦂ B′)
    → (A⊑A′ : A ⊑ A′)
    → (B⊑B′ : B ⊑ B′)
      -----------------------------
    → ⊢lam {Γ} {Σ} {gc} {pc} {ℓᶜ} {A} {B} {N} ⊢N ⊑ ⊢lam {Γ′} {Σ′} {gc′} {pc′} {ℓᶜ} {A′} {B′} {N′} ⊢N′ ⊢ ⊑-ty (l⊑l {ℓ}) (⊑-fun (l⊑l {ℓᶜ}) A⊑A′ B⊑B′)
