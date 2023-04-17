module LabelCoercionCalculi.C where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import LabelCoercionCalculi.Coercion

data LabelExp : Label → Set where

  l : (ℓ : StaticLabel) → LabelExp (l ℓ)

  _⟨_⟩ : ∀ {g₁ g₂} → LabelExp g₁ → ⊢ g₁ ⇒ g₂ → LabelExp g₂

  bl : ∀ {g} (p : BlameLabel) → LabelExp g

data LabelVal : ∀ {g} → LabelExp g → Set where

  v-l : ∀ {ℓ} → LabelVal (l ℓ)

  v-! : ∀ {ℓ} → LabelVal (l ℓ ⟨ ℓ ! ⟩)
