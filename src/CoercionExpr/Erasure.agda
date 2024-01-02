module CoercionExpr.Erasure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
ϵ (id (l high)) = high
ϵ (id (l low))  = low
ϵ (id ⋆)        = low
ϵ (c̅ ⨾ c) = ϵ c̅ ⋎ ϵ₁ c
ϵ (⊥ _ _ p) = low  -- placeholder
