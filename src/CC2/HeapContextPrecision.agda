open import Common.Types

module CC2.HeapContextPrecision where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax hiding (_⨟_)
open import Common.Utils
open import CC2.Statics
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)
open import Memory.HeapContext


data _⊑*_ : (Γ Γ′ : Context) → Set where

  ⊑*-∅ : [] ⊑* []

  ⊑*-∷ : ∀ {Γ Γ′ A A′} → A ⊑ A′ → Γ ⊑* Γ′ → (A ∷ Γ) ⊑* (A′ ∷ Γ′)


⊑*→⊑ : ∀ {Γ Γ′ A A′ x} → Γ ⊑* Γ′ → Γ ∋ x ⦂ A → Γ′ ∋ x ⦂ A′ → A ⊑ A′
⊑*→⊑ {x = 0}     (⊑*-∷ A⊑A′ Γ⊑Γ′) refl refl = A⊑A′
⊑*→⊑ {x = suc x} (⊑*-∷ A⊑A′ Γ⊑Γ′) Γ∋x  Γ′∋x = ⊑*→⊑ Γ⊑Γ′ Γ∋x Γ′∋x


data _⊑ₕ_ : (Σ Σ′ : HalfHeapContext) → Set where

  ⊑-∅ : [] ⊑ₕ []

  ⊑-∷ : ∀ {Σ Σ′ T T′ n} → T ⊑ᵣ T′ → Σ ⊑ₕ Σ′ → (⟨ n , T ⟩ ∷ Σ) ⊑ₕ (⟨ n , T′ ⟩ ∷ Σ′)

_⊑ₘ_ : (Σ Σ′ : HeapContext) → Set
⟨ Σᴸ , Σᴴ ⟩ ⊑ₘ ⟨ Σᴸ′ , Σᴴ′ ⟩ = (Σᴸ ⊑ₕ Σᴸ′) × (Σᴴ ⊑ₕ Σᴴ′)

⊑ₕ→⊑-forward : ∀ {Σ Σ′ T n}
  → Σ ⊑ₕ Σ′
  → find _≟_ Σ  n ≡ just T
    --------------------------------------
  → ∃[ T′ ] (find _≟_ Σ′ n ≡ just T′) × (T ⊑ᵣ T′)
⊑ₕ→⊑-forward {⟨ n₀ , T ⟩ ∷ _} {⟨ n₀ , T′ ⟩ ∷ _} {n = n} (⊑-∷ T⊑T′ Σ⊑Σ′) eq
  with n ≟ n₀
... | no _ = ⊑ₕ→⊑-forward Σ⊑Σ′ eq
... | yes refl with eq
... | refl = ⟨ _ , refl , T⊑T′ ⟩

⊑ₘ→⊑-forward : ∀ {Σ Σ′ T n ℓ̂}
  → Σ ⊑ₘ Σ′
  → let a = a⟦ ℓ̂ ⟧ n in
     lookup-Σ Σ  a ≡ just T
  ------------------------------
  → ∃[ T′ ] (lookup-Σ Σ′ a ≡ just T′) × (T ⊑ᵣ T′)
⊑ₘ→⊑-forward {ℓ̂ = low}  ⟨ Σᴸ⊑ , _ ⟩ Σa≡T = ⊑ₕ→⊑-forward Σᴸ⊑ Σa≡T
⊑ₘ→⊑-forward {ℓ̂ = high} ⟨ _ , Σᴴ⊑ ⟩ Σa≡T = ⊑ₕ→⊑-forward Σᴴ⊑ Σa≡T

⊑ₕ→⊑-backward : ∀ {Σ Σ′ T′ n}
  → Σ ⊑ₕ Σ′
  → find _≟_ Σ′ n ≡ just T′
    --------------------------------------
  → ∃[ T ] (find _≟_ Σ n ≡ just T) × (T ⊑ᵣ T′)
⊑ₕ→⊑-backward {⟨ n₀ , T ⟩ ∷ _} {⟨ n₀ , T′ ⟩ ∷ _} {n = n} (⊑-∷ T⊑T′ Σ⊑Σ′) eq
  with n ≟ n₀
... | no _ = ⊑ₕ→⊑-backward Σ⊑Σ′ eq
... | yes refl with eq
... | refl = ⟨ _ , refl , T⊑T′ ⟩

⊑ₘ→⊑-backward : ∀ {Σ Σ′ T′ n ℓ̂}
  → Σ ⊑ₘ Σ′
  → let a = a⟦ ℓ̂ ⟧ n in
     lookup-Σ Σ′ a ≡ just T′
  ------------------------------
  → ∃[ T ] (lookup-Σ Σ a ≡ just T) × (T ⊑ᵣ T′)
⊑ₘ→⊑-backward {ℓ̂ = low}  ⟨ Σᴸ⊑ , _ ⟩ Σa≡T = ⊑ₕ→⊑-backward Σᴸ⊑ Σa≡T
⊑ₘ→⊑-backward {ℓ̂ = high} ⟨ _ , Σᴴ⊑ ⟩ Σa≡T = ⊑ₕ→⊑-backward Σᴴ⊑ Σa≡T

⊑ₘ→⊑ : ∀ {Σ Σ′ T T′ n ℓ̂}
  → Σ ⊑ₘ Σ′
  → let a = a⟦ ℓ̂ ⟧ n in
     lookup-Σ Σ  a ≡ just T
  → lookup-Σ Σ′ a ≡ just T′
  → T ⊑ᵣ T′
⊑ₘ→⊑ {Σ} {Σ′} {T} {T′} {n} {ℓ̂} Σ⊑Σ′ eq eq′
  with ⊑ₘ→⊑-forward {ℓ̂ = ℓ̂} Σ⊑Σ′ eq
... | ⟨ T″ , eq″ , T⊑T″ ⟩ with trans (sym eq′) eq″
... | refl = T⊑T″
