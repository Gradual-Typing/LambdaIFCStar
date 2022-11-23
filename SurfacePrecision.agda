module SurfacePrecision where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import SurfaceSyntax

infix 6 _⊑ˢ_

data _⊑ˢ_ : Term → Term → Set where

  ⊑ˢ-const : ∀ {ι} {k : rep ι} {ℓ}
      ---------------------------------
    → $ k of ℓ ⊑ˢ $ k of ℓ
