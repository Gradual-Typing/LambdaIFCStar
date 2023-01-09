module CCExpSub.CheckPrecision where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List hiding ([_])
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Common.Utils
open import Common.Types
open import Memory.Addr
open import CCExpSub.Statics


infix 2 check_⊑?_

{- NOTE: Each case of the `check` function below reflects its corresponding rule in `Precision` -}
check_⊑?_ : Term → Term → 𝔹
-- Var
check ` x ⊑? ` y =
  case x ≟ y of λ where
  (yes refl) → true
  (no  _) → false
-- Const
check op-const {ι} k ℓ ⦅ nil ⦆ ⊑? op-const {ι′} k′ ℓ′ ⦅ nil ⦆ =
  case ` ι ≡ᵣ? ` ι′ of λ where
  (yes refl) →
    case ⟨ const-eq? k k′ , ℓ =? ℓ′ ⟩ of λ where
    ⟨ yes refl , yes refl ⟩ → true
    _  → false
  (no _) → false
-- Addr
check addr a of ℓ ⊑? addr a′ of ℓ′ =
  case ⟨ addr-eq? a a′ , ℓ =? ℓ′ ⟩ of λ where
  ⟨ yes refl , yes refl ⟩ → true
  _ → false
-- Lam
check ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ ⊑? ƛ⟦ ℓᶜ′ ⟧ A′ ˙ N′ of ℓ′ =
  case ⟨ ℓᶜ =? ℓᶜ′ , ℓ =? ℓ′ ⟩ of λ where
  ⟨ yes refl , yes refl ⟩ →
    case ⟨ A ⊑? A′ , check N ⊑? N′ ⟩ of λ where
    ⟨ yes _ , true ⟩ → true
    _ → false
  _ → false
-- App
check L · M ⊑? L′ · M′ =
  case ⟨ check L ⊑? L′ , check M ⊑? M′ ⟩ of λ where
  ⟨ true , true ⟩ → true
  _ → false
check _ ⊑? _ = false
