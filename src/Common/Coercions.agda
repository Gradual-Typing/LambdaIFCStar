{- Coercions on terms -}

module Common.Coercions where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_; case_return_of_)

open import Common.Types
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp


infix 6 Castᵣ_⇒_
infix 6 Cast_⇒_

data Castᵣ_⇒_ : RawType → RawType → Set
data Cast_⇒_  : Type → Type → Set

data Castᵣ_⇒_ where

  id  : ∀ ι → Castᵣ ` ι ⇒ ` ι

  ref : ∀ {A B}
    → (i : Cast B ⇒ A)
    → (o : Cast A ⇒ B)
    → Castᵣ Ref A ⇒ Ref B

  fun : ∀ {g₁ g₂} {A B C D}
    → CoercionExp g₂ ⇒ g₁
    → (i : Cast C ⇒ A)
    → (o : Cast B ⇒ D)
    → Castᵣ ⟦ g₁ ⟧ A ⇒ B ⇒ ⟦ g₂ ⟧ C ⇒ D


data Cast_⇒_ where
  cast : ∀ {S T g₁ g₂}
    → Castᵣ S ⇒ T
    → CoercionExp g₁ ⇒ g₂
    → Cast S of g₁ ⇒ T of g₂
