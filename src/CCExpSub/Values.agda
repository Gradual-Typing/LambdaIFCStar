module CCExpSub.Values where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Common.Types
open import Common.TypeBasedCast
open import Common.SubtypeCast
open import CCExpSub.Syntax Cast_⇒_


data Err : Term → Set where
  E-error : ∀ {A} {e : Error} → Err (error A e)

{-
  non-classifying: true of low ⟨ Bool of low ↟ Bool of high ⟩
  classifying:     true of high
-}

data SimpleValue : Term → Set
data Value : Term → Set

data SimpleValue where
  V-const   : ∀ {ι} {k : rep ι} {ℓ} → SimpleValue ($ k of ℓ)
  V-addr    : ∀ {a ℓ} → SimpleValue (addr a of ℓ)
  V-ƛ       : ∀ {pc A N ℓ} → SimpleValue (ƛ⟦ pc ⟧ A ˙ N of ℓ)
  V-cast    : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → SimpleValue (V ⟨ c ⟩)

data Value where
  V-val : ∀ {V} → SimpleValue V → Value V
  V-↟  : ∀ {A B V} {s : A ↟ B} → SimpleValue V → Value (V ↟⟨ s ⟩)
  V-●  : Value ●
