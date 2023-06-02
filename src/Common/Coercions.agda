{- Coercions on terms -}

module Common.Coercions where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_; case_return_of_)

open import Common.Types
open import Common.BlameLabels
open import LabelCoercionCalculus.CoercionExp hiding (coerce) public


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


{- Irreducible coercions form values -}
data Irreducible : ∀ {A B} → Cast A ⇒ B → Set where
  ir-base : ∀ {ι ℓ g} {c̅ : CoercionExp l ℓ ⇒ g}
    → 𝒱 c̅
    → l ℓ ≢ g  {- c̅ ≢ id -}
    → Irreducible (cast (id ι) c̅)

  ir-ref : ∀ {A B ℓ g}
      {c : Cast B ⇒ A} {d : Cast A ⇒ B} {c̅ : CoercionExp l ℓ ⇒ g}
    → 𝒱 c̅
    → Irreducible (cast (ref c d) c̅)

  ir-fun : ∀ {A B C D ℓ g gᶜ₁ gᶜ₂}
      {c : Cast C ⇒ A} {d : Cast B ⇒ D}
      {c̅ : CoercionExp l ℓ ⇒ g} {d̅ : CoercionExp gᶜ₁ ⇒ gᶜ₂}
    → 𝒱 c̅
    → Irreducible (cast (fun d̅ c d) c̅)


coerceᵣ : ∀ {S T} → S ≲ᵣ T → BlameLabel → Castᵣ S ⇒ T
coerce : ∀ {A B} → A ≲ B → BlameLabel → Cast A ⇒ B

coerceᵣ {` ι} {` ι} ≲-ι p = id ι
coerceᵣ {Ref A} {Ref B} (≲-ref A≲B B≲A) p =
  ref (coerce B≲A p) (coerce A≲B p)
coerceᵣ {⟦ g₁ ⟧ A ⇒ B} {⟦ g₂ ⟧ C ⇒ D} (≲-fun g₂≾g₁ C≲A B≲D) p =
  fun (coerceₗ g₂≾g₁ p) (coerce C≲A p) (coerce B≲D p)

coerce {S of g₁} {T of g₂} (≲-ty g₁≾g₂ S≲T) p =
  cast (coerceᵣ S≲T p) (coerceₗ g₁≾g₂ p)


coerceᵣ-id : ∀ T → Castᵣ T ⇒ T
coerce-id : ∀ A → Cast A ⇒ A

coerceᵣ-id (` ι) = id ι
coerceᵣ-id (Ref A) = ref (coerce-id A) (coerce-id A)
coerceᵣ-id (⟦ g ⟧ A ⇒ B) = fun (id g) (coerce-id A) (coerce-id B)

coerce-id (T of g) = cast (coerceᵣ-id T) (id g)
