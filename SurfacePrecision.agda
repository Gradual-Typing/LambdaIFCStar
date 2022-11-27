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

  ⊑ˢ-var : ∀ {x} → ` x ⊑ˢ ` x

  ⊑ˢ-lam : ∀ {pc A A′ N N′ ℓ}
    → A ⊑  A′
    → N ⊑ˢ N′
      -----------------------------------------------
    → ƛ⟦ pc ⟧ A ˙ N of ℓ ⊑ˢ ƛ⟦ pc ⟧ A′ ˙ N′ of ℓ

  ⊑ˢ-app : ∀ {L L′ M M′} {p q}
    → L ⊑ˢ L′
    → M ⊑ˢ M′
      ---------------------
    → L · M at p ⊑ˢ L′ · M′ at q

  ⊑ˢ-if : ∀ {L L′ M M′ N N′} {p q}
    → L ⊑ˢ L′
    → M ⊑ˢ M′
    → N ⊑ˢ N′
      -----------------------------------------------------------
    → if L then M else N at p ⊑ˢ if L′ then M′ else N′ at q

  ⊑ˢ-ann : ∀ {M M′ A A′} {p q}
    → M ⊑ˢ M′
    → A ⊑  A′
      -------------------------------
    → M ∶ A at p ⊑ˢ M′ ∶ A′ at q

  ⊑ˢ-let : ∀ {M M′ N N′}
    → M ⊑ˢ M′
    → N ⊑ˢ N′
      ---------------------------------
    → `let M `in N ⊑ˢ `let M′ `in N′

  ⊑ˢ-ref : ∀ {M M′ ℓ} {p q}
    → M ⊑ˢ M′
      ----------------------------------------
    → ref⟦ ℓ ⟧ M at p ⊑ˢ ref⟦ ℓ ⟧ M′ at q

  ⊑ˢ-deref : ∀ {M M′}
    → M ⊑ˢ M′
      --------------
    → ! M ⊑ˢ ! M′

  ⊑ˢ-assign : ∀ {L L′ M M′} {p q}
    → L ⊑ˢ L′
    → M ⊑ˢ M′
      -------------------------------
    → L := M at p ⊑ˢ L′ := M′ at q
