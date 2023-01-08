module Memory.Addr where

open import Data.Nat
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.SecurityLabels


RawAddr = ℕ

data Addr : Set where
  a⟦_⟧_ : StaticLabel → RawAddr → Addr


addr-eq? : ∀ (a₁ a₂ : Addr) → Dec (a₁ ≡ a₂)
addr-eq? (a⟦ ℓ̂₁ ⟧ n₁) (a⟦ ℓ̂₂ ⟧ n₂) =
  case ℓ̂₁ =? ℓ̂₂ of λ where
  (yes refl) →
    case n₁ ≟ n₂ of λ where
    (yes refl) → yes refl
    (no  neq)  → no λ { refl → contradiction refl neq }
  (no  neq)  → no λ { refl → contradiction refl neq }
