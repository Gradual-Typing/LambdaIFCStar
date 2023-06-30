module CoercionExpr.SecurityLevel where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
open import CoercionExpr.Precision


∥_∥ : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → CVal c̅ → StaticLabel
∥ id (l ℓ) ∥ id = ℓ
∥ id (l ℓ) ⨾ ℓ ! ∥ (inj id) = ℓ
∥ id (l low) ⨾ ↑ ⨾ high ! ∥ (inj (up v)) = high
∥ id (l low) ⨾ ↑ ∥ (up v) = high

level-prec : ∀ {ℓ ℓ′ g g′} (c̅ : CExpr l ℓ ⇒ g) (c̅′ : CExpr l ℓ′ ⇒ g′)
  → (v : CVal c̅)
  → (v′ : CVal c̅′)
  → ⊢ c̅ ⊑ c̅′
    --------------------------------
  → ∥ c̅ ∥ v ≼ ∥ c̅′ ∥ v′
level-prec (id (l _)) (id (l _)) id id (⊑-id l⊑l) = ≼-refl
level-prec (id (l _)) (_ ⨾ (_ !)) id (inj v′) (⊑-castr _ _ ())
level-prec (id (l ℓ)) (id (l low) ⨾ ↑) id (up id) c̅⊑c̅′ = ℓ ≼high
level-prec (_ ⨾ (_ !)) (id (l _)) (inj id) id (⊑-castl c̅⊑c̅′ l⊑l ⋆⊑) = ≼-refl
level-prec (id (l low) ⨾ ↑ ⨾ (_ !)) (id (l high)) (inj (up id)) id (⊑-castl c̅⊑c̅′ l⊑l ⋆⊑) = h≼h
level-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj id) (inj id) (⊑-cast (⊑-id l⊑l) l⊑l _) = ≼-refl
level-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj id) (inj id) (⊑-castr (⊑-castl c̅⊑c̅′ l⊑l _) _ _) = ≼-refl
level-prec (_ ⨾ (ℓ !)) (_ ⨾ (_ !)) (inj id) (inj (up id)) c̅⊑c̅′ = ℓ ≼high
level-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj id) (⊑-cast (⊑-castl _ () _) l⊑l _)
level-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj (up id)) (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l _) = h≼h
level-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj (up id)) (⊑-cast (⊑-castr (⊑-castl _ _ ()) _ _) l⊑l _)
level-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj id) (⊑-castr (⊑-castl c̅⊑c̅′ l⊑l _) _ _) = h≼h
level-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj (up id)) (⊑-castr c̅⊑c̅′ _ _) = h≼h
level-prec (_ ⨾ (ℓ !)) (_ ⨾ ↑) (inj id) (up id) c̅⊑c̅′ = ℓ ≼high
level-prec (_ ⨾ (_ !)) (_ ⨾ ↑) (inj (up id)) (up id) c̅⊑c̅′ = h≼h
level-prec (_ ⨾ ↑) .(id (l _)) (up id) id (⊑-castl c̅⊑c̅′ l⊑l ())
level-prec (_ ⨾ ↑) .(id (l _) ⨾ (_ !)) (up id) (inj id) (⊑-cast c̅⊑c̅′ l⊑l ())
level-prec (_ ⨾ ↑) .(id (l _) ⨾ (_ !)) (up id) (inj id) (⊑-castl c̅⊑c̅′ () _)
level-prec (_ ⨾ ↑) .(id (l _) ⨾ (_ !)) (up id) (inj id) (⊑-castr c̅⊑c̅′ _ ())
level-prec (_ ⨾ ↑) .(id (l low) ⨾ ↑ ⨾ (high !)) (up id) (inj (up id)) c̅⊑c̅′ = h≼h
level-prec (_ ⨾ ↑) .(id (l low) ⨾ ↑) (up id) (up id) c̅⊑c̅′ = h≼h
