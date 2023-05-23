module LabelCoercionCalculus.Stamping where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp
open import LabelCoercionCalculus.SecurityLevel


stamp : ∀ {ℓ g} → (c̅ : CoercionExp l ℓ ⇒ g) → 𝒱 c̅ → (ℓ′ : StaticLabel)
  → CoercionExp l ℓ ⇒ (g ⋎̃ l ℓ′)
stamp {g = g} c̅ v low rewrite g⋎̃low≡g {g} = c̅
stamp (id (l low)) id high = id (l low) ⨾ ↑
stamp (id (l high)) id high = id (l high)
stamp (id (l low) ⨾ low !) (inj id) high = id (l low) ⨾ ↑ ⨾ high !
stamp (id (l high) ⨾ high !) (inj id) high = id (l high) ⨾ high !
stamp (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = id (l low) ⨾ ↑ ⨾ high !
stamp (id (l low) ⨾ ↑) (up id) high = id (l low) ⨾ ↑

stamp-𝒱 : ∀ {ℓ g} → (c̅ : CoercionExp l ℓ ⇒ g) → (v : 𝒱 c̅) → (ℓ′ : StaticLabel)
  → 𝒱 (stamp c̅ v ℓ′)
stamp-𝒱 {g = g} c̅ v low rewrite g⋎̃low≡g {g} = v
stamp-𝒱 (id (l low)) id high = up id
stamp-𝒱 (id (l high)) id high = id
stamp-𝒱 (id (l low) ⨾ low !) (inj id) high = inj (up id)
stamp-𝒱 (id (l high) ⨾ high !) (inj id) high = inj id
stamp-𝒱 (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = inj (up id)
stamp-𝒱 (id (l low) ⨾ ↑) (up id) high = up id

{- coercion stamping is correct with respect to security level -}
stamp-level : ∀ {ℓ g} (c̅ : CoercionExp l ℓ ⇒ g) → (v : 𝒱 c̅) → (ℓ′ : StaticLabel)
  → ∥ stamp c̅ v ℓ′ ∥ (stamp-𝒱 c̅ v ℓ′) ≡ (∥ c̅ ∥ v) ⋎ ℓ′
stamp-level {g = g} c̅ v low
  rewrite g⋎̃low≡g {g} | ℓ⋎low≡ℓ {∥ c̅ ∥ v} = refl
stamp-level (id (l low)) id high = refl
stamp-level (id (l high)) id high = refl
stamp-level (id (l low) ⨾ low !) (inj id) high = refl
stamp-level (id (l high) ⨾ high !) (inj id) high = refl
stamp-level (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = refl
stamp-level (id (l low) ⨾ ↑) (up id) high = refl
