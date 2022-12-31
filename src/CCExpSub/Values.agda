module CCExpSub.Values where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Common.Types
open import Common.TypeBasedCast
open import CCExpSub.Syntax Cast_⇒_


data Err : Term → Set where
  E-error : ∀ {A} {e : Error} → Err (error A e)

data Value : Term → Set where
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-const↟ : ∀ {A B} {ι} {k : rep ι} {ℓ} {A<:B : A <: B}
    → A ≢ B → Value ($ k of ℓ ↟ A<:B)
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-addr↟ : ∀ {A B} {a ℓ} {A<:B : A <: B}
    → A ≢ B → Value (addr a of ℓ ↟ A<:B)
  V-ƛ : ∀ {pc A N ℓ} → Value (ƛ⟦ pc ⟧ A ˙ N of ℓ)
  V-ƛ↟ : ∀ {A₁ A₂} {pc A N ℓ} {A₁<:A₂ : A₁ <: A₂}
    → A₁ ≢ A₂ → Value (ƛ⟦ pc ⟧ A ˙ N of ℓ ↟ A₁<:A₂)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → Value (V ⟨ c ⟩)
  V-cast↟ : ∀ {A B C V} {c : Cast A ⇒ B} {B<:C : B <: C}
    → Value V → Inert c → B ≢ C → Value ((V ⟨ c ⟩) ↟ B<:C)
  V-● : Value ●
