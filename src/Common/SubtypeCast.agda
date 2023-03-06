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

branch/s : ∀ {g₁ g₂} A (s : ` Bool of g₁ ↟ ` Bool of g₂)
  → (stamp A g₁) ↟ (stamp A g₂)
branch/s {g₁} {g₂} A (cast↟ .(` Bool of g₁) .(` Bool of g₂) (<:-ty g₁<:g₂ <:-ι)) =
  cast↟ (stamp A g₁) (stamp A g₂) (stamp-<: <:-refl g₁<:g₂)
