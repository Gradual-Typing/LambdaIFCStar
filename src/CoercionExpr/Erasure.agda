module CoercionExpr.Erasure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr


ϵ₁ : ∀ {g₁ g₂} → ⊢ g₁ ⇒ g₂ → StaticLabel
ϵ₁ (id (l high)) = high
ϵ₁ (id (l low))  = low
ϵ₁ (id ⋆)        = low
ϵ₁ ↑            = high
ϵ₁ (high !)      = high
ϵ₁ (low  !)      = low
ϵ₁ (high ?? p)   = high
ϵ₁ (low  ?? p)   = low

ϵ : ∀ {g₁ g₂} → CExpr g₁ ⇒ g₂ → StaticLabel
ϵ (c̅ ⨾ c) = ϵ c̅ ⋎ ϵ₁ c
ϵ (id (l high)) = high
ϵ (id (l low))  = low
ϵ (id ⋆)        = low
ϵ (⊥ _ _ p)     = high  -- placeholder


{- Properties of erasure -}
ϵ-high : ∀ {g}
  → (c̅ : CExpr g ⇒ l high)
  → ϵ c̅ ≡ high
ϵ-high (id (l high)) = refl
ϵ-high (c̅ ⨾ id (l high)) rewrite ℓ⋎high≡high {ϵ c̅} = refl
ϵ-high (c̅ ⨾ ↑)          rewrite ℓ⋎high≡high {ϵ c̅} = refl
ϵ-high (c̅ ⨾ high ?? p)   rewrite ℓ⋎high≡high {ϵ c̅} = refl
ϵ-high (⊥ _ (l high) p) = refl

ϵ-id : ∀ {g₁ g₂}
  → (c̅ : CExpr g₁ ⇒ g₂)
  → ϵ (c̅ ⨾ id g₂) ≡ ϵ c̅
ϵ-id {g₂ = l high} c̅ rewrite ϵ-high c̅      = refl
ϵ-id {g₂ = l low}  c̅ rewrite ℓ⋎low≡ℓ {ϵ c̅} = refl
ϵ-id {g₂ = ⋆}      c̅ rewrite ℓ⋎low≡ℓ {ϵ c̅} = refl


open import CoercionExpr.SecurityLevel

-- the security of a coercion in normal form agrees with its erasure
ϵ-security-val : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g}
  → (𝓋 : CVal c̅)
  → ϵ c̅ ≡ ∥ c̅ ∥ 𝓋
ϵ-security-val {high} id            = refl
ϵ-security-val {low}  id            = refl
ϵ-security-val {high} (inj id)      = refl
ϵ-security-val {low}  (inj id)      = refl
ϵ-security-val        (inj (up id)) = refl
ϵ-security-val        (up id)       = refl

ϵ-security : ∀ {ℓ g} {c̅ d̅ : CExpr l ℓ ⇒ g}
  → c̅ —↠ d̅
  → (𝓋 : CVal d̅)
  → ϵ c̅ ≡ ∥ d̅ ∥ 𝓋
ϵ-security (_ ∎) 𝓋 = ϵ-security-val 𝓋
ϵ-security (_ —→⟨ ξ r ⟩ r*) v = {!!}
ϵ-security (_ —→⟨ ξ-⊥ ⟩ r*) v = {!!}
ϵ-security (c̅ ⨾ id _ —→⟨ id _ ⟩ r*) v = {!!}
ϵ-security (_ —→⟨ ?-id _ ⟩ r*) v = {!!}
ϵ-security (_ —→⟨ ?-↑ _ ⟩ r*) v = {!!}
ϵ-security (_ —→⟨ ?-⊥ _ ⟩ r*) v = {!!}


-- open import CoercionExpr.SyntacComp

-- c̅ ⨟ d̅
