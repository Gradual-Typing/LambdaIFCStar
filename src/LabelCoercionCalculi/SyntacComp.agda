{- Syntactical composition of coercion expressions -}

module LabelCoercionCalculi.SyntacComp where

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
open import LabelCoercionCalculi.CoercionExp

_⨟_ : ∀ {g₁ g₂ g₃} (c̅₁ : CoercionExp g₁ ⇒ g₂) (c̅₂ : CoercionExp g₂ ⇒ g₃) → CoercionExp g₁ ⇒ g₃
c̅₁ ⨟ ⊥ g₂ g₃ p = ⊥ _ g₃ p
c̅₁ ⨟ id g      = c̅₁ ⨾ id g
c̅₁ ⨟ (c̅₂ ⨾ c)  = (c̅₁ ⨟ c̅₂) ⨾ c
