module Common.CoercePrecision where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Function using (case_of_; case_return_of_)

open import Common.Utils
open import Common.Types
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
  hiding   (Progress; progress)
  renaming (_—→⟨_⟩_ to _—→ₗ⟨_⟩_; _∎ to _∎ₗ ;
            _—→_ to _—→ₗ_; _—↠_ to _—↠ₗ_;
            plug-cong to plug-congₗ)
  public
open import CoercionExpr.SecurityLevel renaming (∥_∥ to ∥_∥ₗ) public
open import CoercionExpr.Stamping
open import CoercionExpr.SyntacComp renaming (_⨟_ to _⊹⊹_)
open import CoercionExpr.Precision
open import Common.Coercions
open import Common.CoercionPrecision


coerceₗ-prec : ∀ {g₁ g₂ g₃ g₄} {p q}
  → g₁ ⊑ₗ g₂
  → g₃ ⊑ₗ g₄
  → (g₁≾g₃ : g₁ ≾ g₃)
  → (g₂≾g₄ : g₂ ≾ g₄)
    ----------------------------------------
  → ⊢ coerceₗ g₁≾g₃ p ⊑ coerceₗ g₂≾g₄ q
coerceₗ-prec {g₂ = l ℓ} ⋆⊑ ⋆⊑ ≾-⋆r ≾-⋆r = ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑
coerceₗ-prec {g₂ = ⋆} ⋆⊑ ⋆⊑ ≾-⋆r ≾-⋆r = ⊑-id ⋆⊑
coerceₗ-prec l⊑l g₃⊑g₄ ≾-⋆r ≾-⋆r = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
coerceₗ-prec {g₄ = l ℓ} ⋆⊑ ⋆⊑ ≾-⋆r ≾-⋆l = ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑
coerceₗ-prec {g₄ = ⋆} ⋆⊑ ⋆⊑ ≾-⋆r ≾-⋆l = ⊑-id ⋆⊑
coerceₗ-prec ⋆⊑ ⋆⊑ ≾-⋆r (≾-l l≼l) = ⊑-id ⋆⊑
coerceₗ-prec ⋆⊑ ⋆⊑ ≾-⋆r (≾-l l≼h) = ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑
coerceₗ-prec ⋆⊑ ⋆⊑ ≾-⋆r (≾-l h≼h) = ⊑-id ⋆⊑
coerceₗ-prec l⊑l ⋆⊑ ≾-⋆r (≾-l l≼l) = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
coerceₗ-prec l⊑l ⋆⊑ ≾-⋆r (≾-l l≼h) = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
coerceₗ-prec l⊑l ⋆⊑ ≾-⋆r (≾-l h≼h) = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
coerceₗ-prec {g₂ = l ℓ} ⋆⊑ ⋆⊑ ≾-⋆l ≾-⋆r = ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑
coerceₗ-prec {g₂ = ⋆} ⋆⊑ ⋆⊑ ≾-⋆l ≾-⋆r = ⊑-id ⋆⊑
coerceₗ-prec {g₄ = l ℓ} ⋆⊑ ⋆⊑ ≾-⋆l ≾-⋆l = ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑
coerceₗ-prec {g₄ = ⋆} ⋆⊑ ⋆⊑ ≾-⋆l ≾-⋆l = ⊑-id ⋆⊑
coerceₗ-prec ⋆⊑ l⊑l ≾-⋆l ≾-⋆l = ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l
coerceₗ-prec ⋆⊑ ⋆⊑ ≾-⋆l (≾-l l≼l) = ⊑-id ⋆⊑
coerceₗ-prec ⋆⊑ ⋆⊑ ≾-⋆l (≾-l l≼h) = ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑
coerceₗ-prec ⋆⊑ ⋆⊑ ≾-⋆l (≾-l h≼h) = ⊑-id ⋆⊑
coerceₗ-prec ⋆⊑ l⊑l ≾-⋆l (≾-l l≼l) = ⊑-castl (⊑-id ⋆⊑) ⋆⊑ l⊑l
coerceₗ-prec ⋆⊑ l⊑l ≾-⋆l (≾-l l≼h) = ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l
coerceₗ-prec ⋆⊑ l⊑l ≾-⋆l (≾-l h≼h) = ⊑-castl (⊑-id ⋆⊑) ⋆⊑ l⊑l
coerceₗ-prec l⊑l l⊑l (≾-l l≼l) (≾-l l≼l) = ⊑-id l⊑l
coerceₗ-prec l⊑l l⊑l (≾-l l≼h) (≾-l l≼h) = ⊑-cast (⊑-id l⊑l) l⊑l l⊑l
coerceₗ-prec l⊑l l⊑l (≾-l h≼h) (≾-l h≼h) = ⊑-id l⊑l

coerce-prec : ∀ {A A′ B B′} {p q}
  → A  ⊑ A′
  → B  ⊑ B′
  → (A≲B   : A  ≲ B )
  → (A′≲B′ : A′ ≲ B′)
    ----------------------------------------
  → ⟨ coerce A≲B p ⟩⊑⟨ coerce A′≲B′ q ⟩
coerce-prec (⊑-ty g₁⊑g₂ ⊑-ι) (⊑-ty g₃⊑g₄ ⊑-ι) (≲-ty g₁≲g₃ ≲-ι) (≲-ty g₂≲g₄ ≲-ι) =
  ⊑-base {!!}
coerce-prec A⊑A′ B⊑B′ (≲-ty x (≲-ref x₁ x₄)) (≲-ty x₂ (≲-ref x₃ x₅)) = {!!}
coerce-prec A⊑A′ B⊑B′ (≲-ty x (≲-fun x₁ x₄ x₅)) (≲-ty x₂ (≲-fun x₃ x₆ x₇)) = {!!}
