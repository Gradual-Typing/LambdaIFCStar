module CoercionExpr.Stamping where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
open import CoercionExpr.SecurityLevel


{- stampₗs a coercion expression -}
stampₗ : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → 𝒱 c̅ → (ℓ′ : StaticLabel)
  → CExpr l ℓ ⇒ (g ⋎̃ l ℓ′)
stampₗ {g = g} c̅ v low rewrite g⋎̃low≡g {g} = c̅
stampₗ (id (l low)) id high = id (l low) ⨾ ↑
stampₗ (id (l high)) id high = id (l high)
stampₗ (id (l low) ⨾ low !) (inj id) high = id (l low) ⨾ ↑ ⨾ high !
stampₗ (id (l high) ⨾ high !) (inj id) high = id (l high) ⨾ high !
stampₗ (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = id (l low) ⨾ ↑ ⨾ high !
stampₗ (id (l low) ⨾ ↑) (up id) high = id (l low) ⨾ ↑


stampₗ-𝒱 : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → (v : 𝒱 c̅) → (ℓ′ : StaticLabel)
  → 𝒱 (stampₗ c̅ v ℓ′)
stampₗ-𝒱 {g = g} c̅ v low rewrite g⋎̃low≡g {g} = v
stampₗ-𝒱 (id (l low)) id high = up id
stampₗ-𝒱 (id (l high)) id high = id
stampₗ-𝒱 (id (l low) ⨾ low !) (inj id) high = inj (up id)
stampₗ-𝒱 (id (l high) ⨾ high !) (inj id) high = inj id
stampₗ-𝒱 (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = inj (up id)
stampₗ-𝒱 (id (l low) ⨾ ↑) (up id) high = up id

{- coercion stampₗing is correct with respect to security level -}
stampₗ-level : ∀ {ℓ g} (c̅ : CExpr l ℓ ⇒ g) → (v : 𝒱 c̅) → (ℓ′ : StaticLabel)
  → ∥ stampₗ c̅ v ℓ′ ∥ (stampₗ-𝒱 c̅ v ℓ′) ≡ (∥ c̅ ∥ v) ⋎ ℓ′
stampₗ-level {g = g} c̅ v low
  rewrite g⋎̃low≡g {g} | ℓ⋎low≡ℓ {∥ c̅ ∥ v} = refl
stampₗ-level (id (l low)) id high = refl
stampₗ-level (id (l high)) id high = refl
stampₗ-level (id (l low) ⨾ low !) (inj id) high = refl
stampₗ-level (id (l high) ⨾ high !) (inj id) high = refl
stampₗ-level (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = refl
stampₗ-level (id (l low) ⨾ ↑) (up id) high = refl

stampₗ-low : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g}
  → (𝓋 : 𝒱 c̅)
  → subst (λ □ → CExpr l ℓ ⇒ □) g⋎̃low≡g (stampₗ c̅ 𝓋 low) ≡ c̅
stampₗ-low (id {l low}) = refl
stampₗ-low (id {l high}) = refl
stampₗ-low (inj id) = refl
stampₗ-low (inj (up id)) = refl
stampₗ-low (up id) = refl
