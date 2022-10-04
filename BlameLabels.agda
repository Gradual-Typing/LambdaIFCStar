module BlameLabels where

open import Data.Nat
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

data BlameLabel : Set where
  pos : ℕ → BlameLabel
  neg : ℕ → BlameLabel

flip : BlameLabel → BlameLabel
flip (pos ℓ) = (neg ℓ)
flip (neg ℓ) = (pos ℓ)
