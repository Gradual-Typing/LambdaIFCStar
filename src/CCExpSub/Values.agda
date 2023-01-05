module CCExpSub.Values where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Common.Types
open import Common.TypeBasedCast
open import Common.SubtypeCast
open import CCExpSub.Syntax Cast_⇒_


data Err : Term → Set where
  E-error : ∀ {A} {e : Error} → Err (error A e)

data Value : Term → Set where
  V-const   : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-const↟ : ∀ {A B} {ι} {k : rep ι} {ℓ} {s : A ↟ B}
    → A ≢ B → Value ($ k of ℓ ↟⟨ s ⟩)
  V-addr    : ∀ {a ℓ} → Value (addr a of ℓ)
  V-addr↟  : ∀ {A B} {a ℓ} {s : A ↟ B}
    → A ≢ B → Value (addr a of ℓ ↟⟨ s ⟩)
  V-ƛ       : ∀ {pc A N ℓ} → Value (ƛ⟦ pc ⟧ A ˙ N of ℓ)
  V-ƛ↟     : ∀ {pc A B C N ℓ} {s : B ↟ C}
    → B ≢ C → Value (ƛ⟦ pc ⟧ A ˙ N of ℓ ↟⟨ s ⟩)
  V-cast    : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → Value (V ⟨ c ⟩)
  V-cast↟  : ∀ {A B C V} {c : Cast A ⇒ B} {s : B ↟ C}
    → Value V → Inert c → B ≢ C → Value ((V ⟨ c ⟩) ↟⟨ s ⟩)
  V-●      : Value ●
