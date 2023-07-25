module CoercionExpr.Stamping where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
open import CoercionExpr.SecurityLevel
open import CoercionExpr.Precision


{- stampₗs a coercion expression -}
stampₗ : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → CVal c̅ → (ℓ′ : StaticLabel)
  → CExpr l ℓ ⇒ (g ⋎̃ l ℓ′)
stampₗ {g = g} c̅ v low rewrite g⋎̃low≡g {g} = c̅
stampₗ (id (l low)) id high = id (l low) ⨾ ↑
stampₗ (id (l high)) id high = id (l high)
stampₗ (id (l low) ⨾ low !) (inj id) high = id (l low) ⨾ ↑ ⨾ high !
stampₗ (id (l high) ⨾ high !) (inj id) high = id (l high) ⨾ high !
stampₗ (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = id (l low) ⨾ ↑ ⨾ high !
stampₗ (id (l low) ⨾ ↑) (up id) high = id (l low) ⨾ ↑


stampₗ-CVal : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → (v : CVal c̅) → (ℓ′ : StaticLabel)
  → CVal (stampₗ c̅ v ℓ′)
stampₗ-CVal {g = g} c̅ v low rewrite g⋎̃low≡g {g} = v
stampₗ-CVal (id (l low)) id high = up id
stampₗ-CVal (id (l high)) id high = id
stampₗ-CVal (id (l low) ⨾ low !) (inj id) high = inj (up id)
stampₗ-CVal (id (l high) ⨾ high !) (inj id) high = inj id
stampₗ-CVal (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = inj (up id)
stampₗ-CVal (id (l low) ⨾ ↑) (up id) high = up id

{- coercion stampₗing is correct with respect to security level -}
stampₗ-security : ∀ {ℓ g}
  → (c̅ : CExpr l ℓ ⇒ g)
  → (v : CVal c̅)
  → (ℓ′ : StaticLabel)
    ---------------------------------------------------------
  → (∥ c̅ ∥ v) ⋎ ℓ′ ≡ ∥ stampₗ c̅ v ℓ′ ∥ (stampₗ-CVal c̅ v ℓ′)
stampₗ-security {g = g} c̅ v low
  rewrite g⋎̃low≡g {g} | ℓ⋎low≡ℓ {∥ c̅ ∥ v} = refl
stampₗ-security (id (l low)) id high = refl
stampₗ-security (id (l high)) id high = refl
stampₗ-security (id (l low) ⨾ low !) (inj id) high = refl
stampₗ-security (id (l high) ⨾ high !) (inj id) high = refl
stampₗ-security (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = refl
stampₗ-security (id (l low) ⨾ ↑) (up id) high = refl


stampₗ-low : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g}
  → (𝓋 : CVal c̅)
  → subst (λ □ → CExpr l ℓ ⇒ □) g⋎̃low≡g (stampₗ c̅ 𝓋 low) ≡ c̅
stampₗ-low (id {l low}) = refl
stampₗ-low (id {l high}) = refl
stampₗ-low (inj id) = refl
stampₗ-low (inj (up id)) = refl
stampₗ-low (up id) = refl


stamp-not-id : ∀ {ℓ ℓ′ g} {c̅ : CExpr l ℓ ⇒ g}
  → CVal c̅
  → l ℓ ≢ g
  → l ℓ ≢ g ⋎̃ l ℓ′
stamp-not-id {low} {low} id neq = neq
stamp-not-id {low} {high} id neq = λ ()
stamp-not-id {high} id neq = neq
stamp-not-id (inj id) neq = neq
stamp-not-id (inj (up id)) neq = neq
stamp-not-id (up id) neq = neq

stampₗ-pres-prec : ∀ {ℓ ℓ₁ ℓ₂ g₁ g₂} {c̅ : CExpr l ℓ₁ ⇒ g₁} {d̅ : CExpr l ℓ₂ ⇒ g₂}
  → (v : CVal c̅)
  → (v′ : CVal d̅)
  → ⊢ c̅ ⊑ d̅
    ------------------------------------
  → ⊢ stampₗ c̅ v ℓ ⊑ stampₗ d̅ v′ ℓ
stampₗ-pres-prec id id (⊑-id l⊑l) = prec-refl _
stampₗ-pres-prec id (inj id) (⊑-castr _ l⊑l ())
stampₗ-pres-prec id (inj (up id)) (⊑-castr _ l⊑l ())
stampₗ-pres-prec id (up id) (⊑-castr _ l⊑l ())
stampₗ-pres-prec {low} {low} (inj id) id (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) =
  ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stampₗ-pres-prec {low} {high} (inj id) id (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) =
  ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stampₗ-pres-prec {high} {low} (inj id) id (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) =
  ⊑-castl (prec-refl _) l⊑l ⋆⊑
stampₗ-pres-prec {high} {high} (inj id) id (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) =
  ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stampₗ-pres-prec (inj (up id)) id (⊑-castl (⊑-castl _ () _) l⊑l ⋆⊑)
stampₗ-pres-prec (inj id) (inj id) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) = prec-refl _
stampₗ-pres-prec (inj (up id)) (inj id) (⊑-cast (⊑-castl _ () l⊑l) l⊑l ⋆⊑)
stampₗ-pres-prec (inj id) (inj (up id)) (⊑-cast (⊑-castr _ () l⊑l) l⊑l ⋆⊑)
stampₗ-pres-prec (inj (up id)) (inj (up id)) (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) = prec-refl _
stampₗ-pres-prec (inj id) (inj id) (⊑-castr (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) = prec-refl _
stampₗ-pres-prec {low} (inj id) (inj (up id)) (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) =
  -- ⊢ id low ; low ! ⊑ id low ; ↑ ; high !
  ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑
stampₗ-pres-prec {high} (inj id) (inj (up id)) (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) =
  prec-refl _
stampₗ-pres-prec (inj id) (inj (up id)) (⊑-castr (⊑-castl (⊑-castr _ () l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑)
stampₗ-pres-prec {low} (inj id) (inj (up id)) (⊑-castr (⊑-castr (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑) =
  ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑
stampₗ-pres-prec {high} (inj id) (inj (up id)) (⊑-castr (⊑-castr (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑) =
  prec-refl _
stampₗ-pres-prec (inj (up id)) (inj id) (⊑-castr (⊑-castl (⊑-castl _ () l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑)
stampₗ-pres-prec (inj (up id)) (inj (up id)) (⊑-castr c̅⊑d̅ _ _) = prec-refl _
stampₗ-pres-prec {low} (inj id) (up id) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stampₗ-pres-prec {high} (inj id) (up id) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) =
  -- ⊢ id low ; ↑ ; high ! ⊑ id low ; ↑
  ⊑-castl (prec-refl _) l⊑l ⋆⊑
stampₗ-pres-prec (inj id) (up id) (⊑-castl (⊑-castr _ () l⊑l) l⊑l ⋆⊑)
stampₗ-pres-prec {low} (inj id) (up id) (⊑-castr (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) =
  -- ⊢ id low ; low ! ⊑ id low ; ↑
  ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stampₗ-pres-prec {high} (inj id) (up id) (⊑-castr (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) =
  ⊑-castl (prec-refl _) l⊑l ⋆⊑
stampₗ-pres-prec {low} (inj (up id)) (up id) (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) =
  ⊑-castl (prec-refl _) l⊑l ⋆⊑
stampₗ-pres-prec {high} (inj (up id)) (up id) (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) =
  ⊑-castl (prec-refl _) l⊑l ⋆⊑
stampₗ-pres-prec (inj (up id)) (up id) (⊑-castr (⊑-castl (⊑-castl _ l⊑l ()) _ _) _ _)
stampₗ-pres-prec (up id) id (⊑-castl _ l⊑l ())
stampₗ-pres-prec (up id) (inj id) (⊑-cast _ _ ())
stampₗ-pres-prec (up id) (inj id) (⊑-castl _ () _)
stampₗ-pres-prec (up id) (inj id) (⊑-castr _ _ ())
stampₗ-pres-prec (up id) (inj (up id)) (⊑-cast _ _ ())
stampₗ-pres-prec (up id) (inj (up id)) (⊑-castl _ () _)
stampₗ-pres-prec (up id) (inj (up id)) (⊑-castr _ _ ())
stampₗ-pres-prec (up id) (up id) c̅⊑d̅ = prec-refl _
