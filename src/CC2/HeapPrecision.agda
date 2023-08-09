open import Common.Types

module CC2.HeapPrecision where

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
open import CC2.Precision
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)
open import Memory.HeapContext


-- ⊑μ-update : ∀ {Σ Σ′} {S T V W} {μ μ′} {n ℓ}
--   → Σ ; Σ′ ⊢ μ ⊑ μ′
--   → [] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ S of l ℓ ⊑ T of l ℓ
--   → (v : Value V)
--   → (w : Value W)
--   -- → lookup-Σ Σ  (a⟦ ℓ ⟧ n) ≡ just S  {- updating a -}
--   -- → lookup-Σ Σ′ (a⟦ ℓ ⟧ n) ≡ just T
--     -------------------------------------------------------------------------
--   → Σ ; Σ′ ⊢ cons-μ (a⟦ ℓ ⟧ n) V v μ ⊑ cons-μ (a⟦ ℓ ⟧ n) W w μ′
-- ⊑μ-update {ℓ = low}  ⟨ μᴸ⊑μᴸ′ , μᴴ⊑μᴴ′ ⟩ V⊑W v w = ⟨ ⊑-∷ μᴸ⊑μᴸ′ V⊑W v w , μᴴ⊑μᴴ′ ⟩
-- ⊑μ-update {ℓ = high} ⟨ μᴸ⊑μᴸ′ , μᴴ⊑μᴴ′ ⟩ V⊑W v w = ⟨ μᴸ⊑μᴸ′ , ⊑-∷ μᴴ⊑μᴴ′ V⊑W v w ⟩


private
  ⊑μ-lookup-low : ∀ {Σ Σ′ T T′} {W w} {μ μ′} {n}
    → Σ ; Σ′ ; low ⊢ μ ⊑ μ′
    → find _≟_ μ′ n ≡ just (W & w)
    → lookup-Σ Σ  (a⟦ low ⟧ n) ≡ just T
    → lookup-Σ Σ′ (a⟦ low ⟧ n) ≡ just T′
      ---------------------------------------------------------------------------------------
    → ∃[ V ] ∃[ v ] (find _≟_ μ n ≡ just (V & v)) ×
         ([] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ T of l low ⊑ T′ of l low)
  ⊑μ-lookup-low {T = T} {T′} {w = w} {n = n}
                (⊑-∷ {n = m} {V} {V′} {S} {S′} μ⊑μ′ V⊑V′ v v′ Σa≡S Σ′a≡S′) eq Σa≡T Σ′a≡T′
    with n ≟ m
  ... | no _ = ⊑μ-lookup-low {w = w} μ⊑μ′ eq Σa≡T Σ′a≡T′
  ... | yes refl
    with trans (sym Σa≡T) Σa≡S | trans (sym Σ′a≡T′) Σ′a≡S′ | eq
  ...   | refl | refl | refl = ⟨ V , v , refl , V⊑V′ ⟩

  ⊑μ-lookup-high : ∀ {Σ Σ′ T T′} {W w} {μ μ′} {n}
    → Σ ; Σ′ ; high ⊢ μ ⊑ μ′
    → find _≟_ μ′ n ≡ just (W & w)
    → lookup-Σ Σ  (a⟦ high ⟧ n) ≡ just T
    → lookup-Σ Σ′ (a⟦ high ⟧ n) ≡ just T′
      ---------------------------------------------------------------------------------------
    → ∃[ V ] ∃[ v ] (find _≟_ μ n ≡ just (V & v)) ×
         ([] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ T of l high ⊑ T′ of l high)
  ⊑μ-lookup-high {T = T} {T′} {w = w} {n = n}
                (⊑-∷ {n = m} {V} {V′} {S} {S′} μ⊑μ′ V⊑V′ v v′ Σa≡S Σ′a≡S′) eq Σa≡T Σ′a≡T′
    with n ≟ m
  ... | no _ = ⊑μ-lookup-high {w = w} μ⊑μ′ eq Σa≡T Σ′a≡T′
  ... | yes refl
    with trans (sym Σa≡T) Σa≡S | trans (sym Σ′a≡T′) Σ′a≡S′ | eq
  ...   | refl | refl | refl = ⟨ V , v , refl , V⊑V′ ⟩

⊑μ-lookup : ∀ {Σ Σ′ S T} {W w} {μ μ′} {ℓ n}
  → Σ ; Σ′ ⊢ μ ⊑ μ′
  → lookup-μ μ′ (a⟦ ℓ ⟧ n) ≡ just (W & w)
  → lookup-Σ Σ  (a⟦ ℓ ⟧ n) ≡ just S
  → lookup-Σ Σ′ (a⟦ ℓ ⟧ n) ≡ just T
    ------------------------------------------------------------------------------------
  → ∃[ V ] ∃[ v ] (lookup-μ μ (a⟦ ℓ ⟧ n) ≡ just (V & v)) ×
        ([] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ S of l ℓ ⊑ T of l ℓ)
⊑μ-lookup {w = w} {ℓ = low}  ⟨ μ⊑μ′ , _ ⟩ = ⊑μ-lookup-low  {w = w} μ⊑μ′
⊑μ-lookup {w = w} {ℓ = high} ⟨ _ , μ⊑μ′ ⟩ = ⊑μ-lookup-high {w = w} μ⊑μ′
