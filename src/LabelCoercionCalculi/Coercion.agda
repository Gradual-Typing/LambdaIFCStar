module LabelCoercionCalculi.Coercion where

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

infixr 10 _;_

data ⊢_⇒_ : Label → Label → Set where

  id : ∀ g → ⊢ g ⇒ g

  ↑ : ⊢ l low ⇒ l high

  _! : ∀ ℓ → ⊢ l ℓ ⇒ ⋆

  _??_ : ∀ ℓ (p : BlameLabel) → ⊢ ⋆ ⇒ l ℓ

  _;_ : ∀ {g₁ g₂ g₃} → ⊢ g₁ ⇒ g₂ → ⊢ g₂ ⇒ g₃ → ⊢ g₁ ⇒ g₃

  ⊥_ : ∀ {g₁ g₂} (p : BlameLabel) → ⊢ g₁ ⇒ g₂
