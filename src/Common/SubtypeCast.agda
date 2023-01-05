module Common.SubtypeCast where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_; case_return_of_)

open import Common.Types


infix 6 _↟_

data _↟_ : Type → Type → Set where
  cast↟ : ∀ A B → A <: B → A ↟ B
