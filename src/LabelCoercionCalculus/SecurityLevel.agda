module LabelCoercionCalculus.SecurityLevel where

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp


∥_∥ : ∀ {ℓ g} → (c̅ : CoercionExp l ℓ ⇒ g) → 𝒱 c̅ → StaticLabel
∥ id (l ℓ) ∥ id = ℓ
∥ id (l ℓ) ⨾ ℓ ! ∥ (inj id) = ℓ
∥ id (l low) ⨾ ↑ ⨾ high ! ∥ (inj (up v)) = high
∥ id (l low) ⨾ ↑ ∥ (up v) = high
