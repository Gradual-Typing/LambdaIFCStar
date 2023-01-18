module CC.MultiStep where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC.CCStatics
open import CC.Reduction

open import CC.TypeSafety


{- Multi-step reduction -}
infix  2 _∣_∣_—↠_∣_
infixr 2 _∣_∣_—→⟨_⟩_
infix  3 _∣_∣_∎

data _∣_∣_—↠_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

    _∣_∣_∎ : ∀ M μ pc
        -----------------------------------
      → M ∣ μ ∣ pc —↠ M ∣ μ

    _∣_∣_—→⟨_⟩_ : ∀ L μ pc {M N μ′ μ″}
      → L ∣ μ  ∣ pc —→ M ∣ μ′
      → M ∣ μ′ ∣ pc —↠ N ∣ μ″
        -----------------------------------
      → L ∣ μ  ∣ pc —↠ N ∣ μ″


multi-pres : ∀ {Σ gc pc M M′ A μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → M ∣ μ ∣ pc —↠ M′ ∣ μ′
    ---------------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; pc ⊢ M′ ⦂ A) × (Σ′ ⊢ μ′)
multi-pres {Σ} ⊢M ⊢μ pc≲gc (_ ∣ _ ∣ _ ∎) =
  ⟨ Σ , ⊇-refl Σ , ⊢M , ⊢μ ⟩
multi-pres ⊢M ⊢μ pc≲gc (M ∣ μ ∣ pc —→⟨ M→N ⟩ N↠M′) =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢N , ⊢μ′ ⟩ = preserve ⊢M ⊢μ pc≲gc M→N in
  let ⟨ Σ″ , Σ″⊇Σ′ , ⊢M′ , ⊢μ″ ⟩ = multi-pres ⊢N ⊢μ′ pc≲gc N↠M′ in
  ⟨ Σ″ , ⊇-trans Σ″⊇Σ′ Σ′⊇Σ , ⊢M′ , ⊢μ″ ⟩

multi-preserve : ∀ {M M′ A μ}
  → [] ; ∅ ; l low ; low ⊢ M ⦂ A
  → M ∣ ∅ ∣ low —↠ M′ ∣ μ
    -----------------------------------------------------
  → ∃[ Σ ] ([] ; Σ ; l low ; low ⊢ M′ ⦂ A) × (Σ ⊢ μ)
multi-preserve ⊢M M↠M′ =
  let ⟨ Σ , _ , ⊢M′ , ⊢μ ⟩ = multi-pres ⊢M ⊢μ-nil (≾-l l≼l) M↠M′ in
  ⟨ Σ , ⊢M′ , ⊢μ ⟩

multi-trans : ∀ {M₁ M₂ M₃ μ₁ μ₂ μ₃ pc}
  → M₁ ∣ μ₁ ∣ pc —↠ M₂ ∣ μ₂
  → M₂ ∣ μ₂ ∣ pc —↠ M₃ ∣ μ₃
  → M₁ ∣ μ₁ ∣ pc —↠ M₃ ∣ μ₃
multi-trans (M ∣ μ ∣ pc ∎) (M ∣ μ ∣ pc ∎) = M ∣ μ ∣ pc ∎
multi-trans (M₁ ∣ μ₁ ∣ pc ∎) (M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃) =
  M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃
multi-trans (M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃) (M₃ ∣ μ₃ ∣ pc ∎) =
  M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃
multi-trans (M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃)
            (M₃ ∣ μ₃ ∣ pc —→⟨ M₃→M₄ ⟩ M₄↠M₅) =
  M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ (multi-trans M₂↠M₃ (M₃ ∣ μ₃ ∣ pc —→⟨ M₃→M₄ ⟩ M₄↠M₅))
