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

-- if a coercion casts a label to high, then its security must be high
ϵ-high : ∀ {g}
  → (c̅ : CExpr g ⇒ l high)
  → ϵ c̅ ≡ high
ϵ-high (id (l high)) = refl
ϵ-high (c̅ ⨾ id (l high)) rewrite ℓ⋎high≡high {ϵ c̅} = refl
ϵ-high (c̅ ⨾ ↑)          rewrite ℓ⋎high≡high {ϵ c̅} = refl
ϵ-high (c̅ ⨾ high ?? p)   rewrite ℓ⋎high≡high {ϵ c̅} = refl
ϵ-high (⊥ _ (l high) p) = refl

ϵ-ϵ₁-id : ∀ {g} → ϵ (id g) ≡ ϵ₁ (id g)
ϵ-ϵ₁-id {⋆}      = refl
ϵ-ϵ₁-id {l high} = refl
ϵ-ϵ₁-id {l low}  = refl

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

ϵ-security-step : ∀ {g₁ g₂} {c̅ d̅ : CExpr g₁ ⇒ g₂}
  → c̅ —→ d̅
  → ϵ c̅ ≡ ϵ d̅
ϵ-security-step (ξ r) rewrite ϵ-security-step r = refl
ϵ-security-step ξ-⊥ = refl
ϵ-security-step {c̅ = c̅ ⨾ c} (id _) rewrite ϵ-id c̅ = refl
ϵ-security-step {g₁} {l high} {c̅ = c̅ ⨾ high ! ⨾ high ?? p} (?-id _)
  rewrite ϵ-high c̅ = refl
ϵ-security-step {g₁} {l low}  {c̅ = c̅ ⨾ low  ! ⨾ low  ?? p} (?-id _)
  rewrite ℓ⋎low≡ℓ {ϵ c̅ ⋎ low} | ℓ⋎low≡ℓ {ϵ c̅} = refl
ϵ-security-step {c̅ = c̅ ⨾ low ! ⨾ high ?? p} (?-↑ _) rewrite ℓ⋎low≡ℓ {ϵ c̅} = refl
ϵ-security-step {c̅ = c̅ ⨾ high ! ⨾ low ?? p} (?-⊥ _)
  rewrite ℓ⋎low≡ℓ {ϵ c̅ ⋎ high} | ℓ⋎high≡high {ϵ c̅} = refl

-- the erasure of a coercion agrees with the security after normalization
ϵ-security : ∀ {ℓ g} {c̅ d̅ : CExpr l ℓ ⇒ g}
  → c̅ —↠ d̅
  → (𝓋 : CVal d̅)
  → ϵ c̅ ≡ ∥ d̅ ∥ 𝓋
ϵ-security (_ ∎) 𝓋 = ϵ-security-val 𝓋
ϵ-security (_ —→⟨ r ⟩ r*) v rewrite ϵ-security-step r | ϵ-security r* v = refl


open import CoercionExpr.SyntacComp

-- the erasure of the syntactical composition of two coercions
-- is equal to the join of their respective erasures
ϵ-comp : ∀ {g₁ g₂ g₃} (c̅ : CExpr g₁ ⇒ g₂) (d̅ : CExpr g₂ ⇒ g₃) → ϵ (c̅ ⨟ d̅) ≡ (ϵ c̅) ⋎ (ϵ d̅)
ϵ-comp {g₂ = g₂} c̅ (id _) rewrite ϵ-ϵ₁-id {g₂}                            = refl
ϵ-comp c̅ (d̅ ⨾ c)          rewrite ϵ-comp c̅ d̅ | ⋎-assoc {ϵ c̅} {ϵ d̅} {ϵ₁ c} = refl
ϵ-comp c̅ (⊥ _ _ p)        rewrite ℓ⋎high≡high {ϵ c̅}                       = refl
