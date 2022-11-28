{- Precision relation of the cast calculus -}

open import Types

module CCPrecision (Cast_⇒_ : Type → Type → Set) where

open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import HeapContext
open import CCSyntax Cast_⇒_

infix 4 _;_∣_;_⊢_⊑_

data _;_∣_;_⊢_⊑_ : Context → HeapContext → Context → HeapContext → Term → Term → Set where

  ⊑-const : ∀ {Γ Γ′ Σ Σ′} {ι} {k : rep ι} {ℓ}
      ------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ $ k of ℓ ⊑ $ k of ℓ
