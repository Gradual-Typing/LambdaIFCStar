module Surface2.Precision where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax

open import Common.Utils
open import Common.Types
open import Surface2.Syntax


infix 6 _⊑ᴳ_

data _⊑ᴳ_ : Term → Term → Set where

  ⊑ᴳ-const : ∀ {ι} {k : rep ι} {ℓ}
      ---------------------------------
    → $ k of ℓ ⊑ᴳ $ k of ℓ

  ⊑ᴳ-var : ∀ {x} → ` x ⊑ᴳ ` x

  ⊑ᴳ-lam : ∀ {g g′ A A′ N N′ ℓ}
    → g ⊑ₗ g′
    → A ⊑  A′
    → N ⊑ᴳ N′
      -----------------------------------------------
    → ƛ g , A ˙ N of ℓ ⊑ᴳ ƛ g′ , A′ ˙ N′ of ℓ

  ⊑ᴳ-app : ∀ {L L′ M M′} {p}
    → L ⊑ᴳ L′
    → M ⊑ᴳ M′
      ---------------------
    → L · M at p ⊑ᴳ L′ · M′ at p

  ⊑ᴳ-if : ∀ {L L′ M M′ N N′} {p}
    → L ⊑ᴳ L′
    → M ⊑ᴳ M′
    → N ⊑ᴳ N′
      -----------------------------------------------------------
    → if L then M else N at p ⊑ᴳ if L′ then M′ else N′ at p

  ⊑ᴳ-ann : ∀ {M M′ A A′} {p}
    → M ⊑ᴳ M′
    → A ⊑  A′
      -------------------------------
    → M ∶ A at p ⊑ᴳ M′ ∶ A′ at p

  ⊑ᴳ-let : ∀ {M M′ N N′}
    → M ⊑ᴳ M′
    → N ⊑ᴳ N′
      ---------------------------------
    → `let M `in N ⊑ᴳ `let M′ `in N′

  ⊑ᴳ-ref : ∀ {M M′ ℓ} {p}
    → M ⊑ᴳ M′
      ----------------------------------------
    → ref⟦ ℓ ⟧ M at p ⊑ᴳ ref⟦ ℓ ⟧ M′ at p

  ⊑ᴳ-deref : ∀ {M M′} {p}
    → M ⊑ᴳ M′
      --------------
    → ! M at p ⊑ᴳ ! M′ at p

  ⊑ᴳ-assign : ∀ {L L′ M M′} {p}
    → L ⊑ᴳ L′
    → M ⊑ᴳ M′
      -------------------------------
    → L := M at p ⊑ᴳ L′ := M′ at p
