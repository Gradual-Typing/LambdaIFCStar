{- Coercions on terms -}

module Common.Coercions where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_; case_return_of_)

open import Common.Types
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp public


infix 6 Castᵣ_⇒_
infix 6 Cast_⇒_

data Castᵣ_⇒_ : RawType → RawType → Set
data Cast_⇒_  : Type → Type → Set

data Castᵣ_⇒_ where

  id  : ∀ ι → Castᵣ ` ι ⇒ ` ι

  ref : ∀ {A B}
    → (c : Cast B ⇒ A)  {- in  -}
    → (d : Cast A ⇒ B)  {- out -}
    → Castᵣ Ref A ⇒ Ref B

  fun : ∀ {g₁ g₂} {A B C D}
    → CoercionExp g₂ ⇒ g₁
    → (c : Cast C ⇒ A)  {- in  -}
    → (d : Cast B ⇒ D)  {- out -}
    → Castᵣ ⟦ g₁ ⟧ A ⇒ B ⇒ ⟦ g₂ ⟧ C ⇒ D


data Cast_⇒_ where
  cast : ∀ {S T g₁ g₂}
    → Castᵣ S ⇒ T
    → CoercionExp g₁ ⇒ g₂
    → Cast S of g₁ ⇒ T of g₂


{- Irreducible coercions -}
data Irreducible : ∀ {A B} → Cast A ⇒ B → Set where
  ir-base : ∀ {ι g₁ g₂} {c̅ : CoercionExp g₁ ⇒ g₂}
    → 𝒱 c̅
    → g₁ ≢ g₂  {- c̅ ≢ id -}
    → Irreducible (cast (id ι) c̅)

  ir-ref : ∀ {A B g₁ g₂}
      {c : Cast B ⇒ A} {d : Cast A ⇒ B} {c̅ : CoercionExp g₁ ⇒ g₂}
    → 𝒱 c̅
    → Irreducible (cast (ref c d) c̅)

  ir-fun : ∀ {A B C D g₁ g₂ gᶜ₁ gᶜ₂}
      {c : Cast C ⇒ A} {d : Cast B ⇒ D}
      {c̅ : CoercionExp g₁ ⇒ g₂} {d̅ : CoercionExp gᶜ₁ ⇒ gᶜ₂}
    → 𝒱 c̅
    → Irreducible (cast (fun d̅ c d) c̅)
