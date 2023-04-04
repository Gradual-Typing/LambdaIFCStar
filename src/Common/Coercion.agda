module Common.Coercion where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_; case_return_of_)

open import Common.Types
open import Common.BlameLabels

data LCast_⇒_ : Label → Label → Set where
  id : ∀ (g : Label) → LCast g ⇒ g
  !_ : ∀ (ℓ : StaticLabel) → LCast l ℓ ⇒ ⋆
  _??_ : ∀ (ℓ : StaticLabel) → LCast ⋆ ⇒ l ℓ


data RCast_⇒_ : RawType → RawType → Set
data Cast_⇒_ : Type → Type → Set

data RCast_⇒_ where
  id : ∀ {ι} → RCast (` ι) ⇒ (` ι)
  ref : ∀ {A B} → Cast A ⇒ B → RCast (Ref A) ⇒ (Ref B)
  fun : ∀ {g₁ g₂} {A B C D}
    → LCast g₂ ⇒ g₁
    → Cast C ⇒ A
    → Cast B ⇒ D
    → RCast (⟦ g₁ ⟧ A ⇒ B) ⇒ (⟦ g₂ ⟧ C ⇒ D)

data Cast_⇒_ where
  cast : ∀ {S T g₁ g₂}
    → RCast S ⇒ T
    → LCast g₁ ⇒ g₂
    → Cast (S of g₁) ⇒ (T of g₂)
