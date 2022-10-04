module RelatedHeaps where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; subst; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import Heap
open import CC
open import Reduction
open import Utils

open import Erasure


{- Related heaps -}
infix 4 _≈_

_≈_ : ∀ (μ μ′ : Heap) → Set
μ ≈ μ′ = ∀ a {V ℓ}
  → key _≟_ μ a ≡ just ⟨ V , ℓ ⟩
  → case ℓ of λ where
     low  →         key _≟_ μ′ a ≡ just ⟨ erase V , low  ⟩
     high → ∃[ V′ ] key _≟_ μ′ a ≡ just ⟨ V′ , high ⟩

-- a special case for assign-●
μ≈-high-update : ∀ {μ μ′ a V₁ V₂} → μ ≈ μ′ → key _≟_ μ a ≡ just ⟨ V₁ , high ⟩ → ⟨ a , V₂ , high ⟩ ∷ μ ≈ μ′
μ≈-high-update {μ} {μ′} {a₁} {V₁} {V₂} μ≈ eq a {V} {ℓ} with a ≟ a₁
... | yes refl = λ { refl → μ≈ a eq }
... | no  _    = λ eq → μ≈ a eq

μ≈-high : ∀ {μ μ′ a V V′} → μ ≈ μ′ → ⟨ a , V , high ⟩ ∷ μ ≈ ⟨ a , V′ , high ⟩ ∷ μ′
μ≈-high {μ} {μ′} {a₁} {V₁} μ≈ a {ℓ = low} with a ≟ a₁
... | yes _ = λ ()
... | no  _ = λ eq → μ≈ a eq
μ≈-high {μ} {μ′} {a₁} {V₁} {V′} μ≈ a {ℓ = high} with a ≟ a₁
... | yes _ = λ { refl → ⟨ V′ , refl ⟩ }
... | no  _ = λ eq → μ≈ a eq

μ≈-low : ∀ {μ μ′ a V} → μ ≈ μ′ → ⟨ a , V , low ⟩ ∷ μ ≈ ⟨ a , erase V , low ⟩ ∷ μ′
μ≈-low {μ} {μ′} {a₁} {V₁} μ≈ a {ℓ = low}  with a ≟ a₁
... | yes _ = λ { refl → refl }
... | no  _ = λ eq → μ≈ a eq
μ≈-low {μ} {μ′} {a₁} {V₁} μ≈ a {ℓ = high} with a ≟ a₁
... | yes _ = λ ()
... | no _  = λ eq → μ≈ a eq

≈-trans : ∀ {μ₁ μ₂ μ₃} → μ₁ ≈ μ₂ → μ₂ ≈ μ₃ → μ₁ ≈ μ₃
≈-trans {μ₁} {μ₂} {μ₃} μ₁≈μ₂ μ₂≈μ₃ a {V} {low} eq =
  begin
    key _≟_ μ₃ a
    ≡⟨ μ₂≈μ₃ a (μ₁≈μ₂ a eq) ⟩
    just ⟨ erase (erase V) , low ⟩
    ≡⟨ cong (λ □ → just ⟨ □ , low ⟩) (sym (erase-idem V)) ⟩
    just ⟨ erase V , low ⟩
    ∎
≈-trans μ₁≈μ₂ μ₂≈μ₃ a {V} {high} eq =
  let ⟨ V′ , eq′ ⟩ = μ₁≈μ₂ a eq in
  μ₂≈μ₃ a eq′


erase-≈ : ∀ μ → μ ≈ erase-μ μ
erase-≈ [] = λ _ ()
erase-≈ (⟨ a₁ , V₁ , low  ⟩ ∷ μ) a {V} {low} with a ≟ a₁
... | yes _ = λ { refl → refl }
... | no  _ = λ eq → erase-≈ μ a eq
erase-≈ (⟨ a₁ , V₁ , low  ⟩ ∷ μ) a {V} {high} with a ≟ a₁
... | yes _ = λ ()
... | no  _ = λ eq → erase-≈ μ a eq
erase-≈ (⟨ a₁ , V₁ , high ⟩ ∷ μ) a {V} {low} with a ≟ a₁
... | yes _ = λ ()
... | no  _ = λ eq → erase-≈ μ a eq
erase-≈ (⟨ a₁ , V₁ , high ⟩ ∷ μ) a {V} {high} with a ≟ a₁
... | yes _ = λ { refl → ⟨ ● , refl ⟩ }
... | no  _ = λ eq → erase-≈ μ a eq

erase-pres-≈ : ∀ {μ μ′} → μ ≈ μ′ → μ ≈ erase-μ μ′
erase-pres-≈ {μ} {μ′} μ≈μ′ = ≈-trans {μ} {μ′} {erase-μ μ′} μ≈μ′ (erase-≈ μ′)
