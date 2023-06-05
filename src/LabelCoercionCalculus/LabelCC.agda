module LabelCoercionCalculus.LabelCC where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp
  renaming (progress to progressₗ)
open import LabelCoercionCalculus.SyntacComp


data LCCExpr : Set where

  l : StaticLabel → LCCExpr

  _⟪_⟫ : ∀ {g₁ g₂} → LCCExpr → CoercionExp g₁ ⇒ g₂ → LCCExpr

  blame : BlameLabel → LCCExpr


Irreducible : ∀ {g₁ g₂} (c̅ : CoercionExp g₁ ⇒ g₂) → Set
Irreducible {g₁} {g₂} c̅ = 𝒱 c̅ × g₁ ≢ g₂


data LCCVal : LCCExpr → Set where

  {- raw value -}
  v-l : ∀ {ℓ} → LCCVal (l ℓ)

  {- wrapped value (one cast) -}
  v-cast : ∀ {ℓ g} {c̅ : CoercionExp l ℓ ⇒ g}
    → Irreducible c̅
    → LCCVal (l ℓ ⟪ c̅ ⟫)

data ⊢_⇐_ : LCCExpr → Label → Set where

  ⊢l : ∀ {ℓ} → ⊢ l ℓ ⇐ l ℓ

  ⊢cast : ∀ {g₁ g₂} {M} {c̅ : CoercionExp g₁ ⇒ g₂}
    → ⊢ M ⇐ g₁
      ------------------
    → ⊢ M ⟪ c̅ ⟫ ⇐ g₂

  ⊢blame : ∀ {g} {p} → ⊢ blame p ⇐ g


infix 2 _—→ₑ_

data _—→ₑ_ : (M N : LCCExpr) → Set where

  ξ : ∀ {g₁ g₂} {M N} {c̅ : CoercionExp g₁ ⇒ g₂}
    → M —→ₑ N
      --------------------------
    → M ⟪ c̅ ⟫ —→ₑ N ⟪ c̅ ⟫

  ξ-blame : ∀ {g₁ g₂} {c̅ : CoercionExp g₁ ⇒ g₂} {p}
      -----------------------------------------------
    → blame p ⟪ c̅ ⟫ —→ₑ blame p

  β-id : ∀ {ℓ} → l ℓ ⟪ id (l ℓ) ⟫ —→ₑ l ℓ

  cast : ∀ {ℓ g} {c̅ c̅ₙ : CoercionExp l ℓ ⇒ g}
    → c̅ —↠ c̅ₙ
    → 𝒱 c̅ₙ
      -------------------------------
    → l ℓ ⟪ c̅ ⟫ —→ₑ l ℓ ⟪ c̅ₙ ⟫

  blame : ∀ {ℓ g} {c̅ : CoercionExp l ℓ ⇒ g} {p}
    → c̅ —↠ ⊥ (l ℓ) g p
      --------------------------
    → l ℓ ⟪ c̅ ⟫ —→ₑ blame p

  comp : ∀ {ℓ g₁ g₂} {c̅ᵢ : CoercionExp l ℓ ⇒ g₁} {d̅ : CoercionExp g₁ ⇒ g₂}
    → Irreducible c̅ᵢ
      -------------------------------------------
    → l ℓ ⟪ c̅ᵢ ⟫ ⟪ d̅ ⟫ —→ₑ l ℓ ⟪ c̅ᵢ ⨟ d̅ ⟫



data LCCProgress : LCCExpr → Set where

  done : ∀ {M} → LCCVal M → LCCProgress M

  error : ∀ {p} → LCCProgress (blame p)

  step : ∀ {M N} → M  —→ₑ N → LCCProgress M

progress : ∀ {g M} → ⊢ M ⇐ g → LCCProgress M
progress ⊢l = done v-l
progress (⊢cast {c̅ = c̅} ⊢M) =
  case progress ⊢M of λ where
  (done v) →
    case ⟨ v , ⊢M ⟩ of λ where
    ⟨ v-l , ⊢l ⟩ →
      case result c̅ of λ where
      (success c̅↠d̅ 𝓋) → step (cast c̅↠d̅ 𝓋)
      (fail c̅↠⊥)      → step (blame c̅↠⊥)
    ⟨ v-cast {c̅ = c̅′} i , ⊢cast _ ⟩ → step (comp i)
  (error) → step ξ-blame
  (step M→N) → step (ξ M→N)
progress ⊢blame = error
