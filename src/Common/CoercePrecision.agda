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

coerceₗ-prec-left : ∀ {g₁ g₂ g} {p}
  → g₁ ⊑ₗ g
  → g₂ ⊑ₗ g
  → (g₁≾g₂ : g₁ ≾ g₂)
    ----------------------------------------
  → ⊢l coerceₗ g₁≾g₂ p ⊑ g
coerceₗ-prec-left ⋆⊑ ⋆⊑ ≾-⋆r = ⊑-id ⋆⊑
coerceₗ-prec-left ⋆⊑ ⋆⊑ ≾-⋆l = ⊑-id ⋆⊑
coerceₗ-prec-left ⋆⊑ l⊑l ≾-⋆l = ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l
coerceₗ-prec-left l⊑l ⋆⊑ ≾-⋆r = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
coerceₗ-prec-left l⊑l l⊑l (≾-l l≼l) = ⊑-id l⊑l
coerceₗ-prec-left l⊑l l⊑l (≾-l h≼h) = ⊑-id l⊑l

coerce-prec : ∀ {A A′ B B′} {p q}
  → A  ⊑ A′
  → B  ⊑ B′
  → (A≲B   : A  ≲ B )
  → (A′≲B′ : A′ ≲ B′)
    ----------------------------------------
  → ⟨ coerce A≲B p ⟩⊑⟨ coerce A′≲B′ q ⟩
coerce-prec (⊑-ty g₁⊑g₂ ⊑-ι) (⊑-ty g₃⊑g₄ ⊑-ι) (≲-ty g₁≲g₃ ≲-ι) (≲-ty g₂≲g₄ ≲-ι) =
  ⊑-base (coerceₗ-prec g₁⊑g₂ g₃⊑g₄ g₁≲g₃ g₂≲g₄)
coerce-prec (⊑-ty g₁⊑g₃ (⊑-ref A⊑C)) (⊑-ty g₂⊑g₄ (⊑-ref B⊑D))
            (≲-ty g₁≲g₂ (≲-ref A≲B B≲A)) (≲-ty g₃≲g₄ (≲-ref C≲D D≲C)) =
  ⊑-ref (coerce-prec B⊑D A⊑C B≲A D≲C) (coerce-prec A⊑C B⊑D A≲B C≲D) (coerceₗ-prec g₁⊑g₃ g₂⊑g₄ g₁≲g₂ g₃≲g₄)
coerce-prec (⊑-ty g₁⊑g₂ (⊑-fun gc₁⊑gc₂ A⊑C B⊑D)) (⊑-ty g₃⊑g₄ (⊑-fun gc₃⊑gc₄ A′⊑C′ B′⊑D′))
            (≲-ty g₁≲g₃ (≲-fun gc₃≲gc₁ A′≲A B≲B′)) (≲-ty g₂≲g₄ (≲-fun gc₄≲gc₂ C′≲C D≲D′)) =
  ⊑-fun (coerceₗ-prec gc₃⊑gc₄ gc₁⊑gc₂ gc₃≲gc₁ gc₄≲gc₂)
        (coerce-prec A′⊑C′ A⊑C A′≲A C′≲C)
        (coerce-prec B⊑D B′⊑D′ B≲B′ D≲D′)
        (coerceₗ-prec g₁⊑g₂ g₃⊑g₄ g₁≲g₃ g₂≲g₄)


coerce-prec-left : ∀ {A B C} {p}
  → A ⊑ C
  → B ⊑ C
  → (A≲B : A ≲ B)
    ----------------------------------------
  → ⟨ coerce A≲B p ⟩⊑ C
coerce-prec-left (⊑-ty g₁⊑g ⊑-ι) (⊑-ty g₂⊑g ⊑-ι) (≲-ty g₁≲g₂ ≲-ι) =
  ⊑-base (coerceₗ-prec-left g₁⊑g g₂⊑g g₁≲g₂)
coerce-prec-left (⊑-ty g₁⊑g (⊑-ref A⊑C)) (⊑-ty g₂⊑g (⊑-ref B⊑C))
                 (≲-ty g₁≲g₂ (≲-ref A≲B B≲A)) =
  ⊑-ref (coerce-prec-left B⊑C A⊑C B≲A) (coerce-prec-left A⊑C B⊑C A≲B) (coerceₗ-prec-left g₁⊑g g₂⊑g g₁≲g₂)
coerce-prec-left (⊑-ty g₁⊑g (⊑-fun gc₁⊑gc A⊑E B⊑F)) (⊑-ty g₂⊑g (⊑-fun gc₂⊑gc C⊑E D⊑F))
            (≲-ty g₁≲g₂ (≲-fun gc₂≲gc₁ C≲A B≲D)) =
  ⊑-fun (coerceₗ-prec-left gc₂⊑gc gc₁⊑gc gc₂≲gc₁)
        (coerce-prec-left C⊑E A⊑E C≲A)
        (coerce-prec-left B⊑F D⊑F B≲D)
        (coerceₗ-prec-left g₁⊑g g₂⊑g g₁≲g₂)
