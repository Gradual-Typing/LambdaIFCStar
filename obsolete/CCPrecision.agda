{- Precision relation of the cast calculus -}

open import Types

module CCPrecision where

open import Data.Nat
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import HeapContext
open import TypeBasedCast
open import CC

infix 4 _;_∣_;_⊢_⊑_

data _;_∣_;_⊢_⊑_ : Context → HeapContext → Context → HeapContext → Term → Term → Set where

  ⊑-const : ∀ {Γ Γ′ Σ Σ′} {ι} {k : rep ι} {ℓ}
      ------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ $ k of ℓ ⊑ $ k of ℓ

  ⊑-addr : ∀ {Γ Γ′ Σ Σ′} {a ℓ}
      -------------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ addr a of ℓ ⊑ addr a of ℓ

  ⊑-var : ∀ {Γ Γ′ Σ Σ′} {x}
      --------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ ` x ⊑ ` x

  ⊑-lam : ∀ {Γ Γ′ Σ Σ′} {A A′ N N′} {pc ℓ}
    → A ⊑ A′
    → A ∷ Γ ; Σ ∣ A′ ∷ Γ′ ; Σ′ ⊢ N ⊑ N′
      ----------------------------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ ƛ⟦ pc ⟧ A ˙ N of ℓ ⊑ ƛ⟦ pc ⟧ A′ ˙ N′ of ℓ

  ⊑-app : ∀ {Γ Γ′ Σ Σ′} {L L′ M M′}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L ⊑ L′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      --------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L · M ⊑ L′ · M′

  ⊑-if : ∀ {Γ Γ′ Σ Σ′} {A A′ L L′ M M′ N N′}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L ⊑ L′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ N ⊑ N′
      --------------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ if L A M N ⊑ if L′ A′ M′ N′

  ⊑-let : ∀ {Γ Γ′ Σ Σ′} {M M′ N N′}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ N ⊑ N′
      -------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ `let M N ⊑ `let M′ N′

  ⊑-ref : ∀ {Γ Γ′ Σ Σ′} {M M′} {ℓ}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ---------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ ref⟦ ℓ ⟧ M ⊑ ref⟦ ℓ ⟧ M′

  ⊑-ref? : ∀ {Γ Γ′ Σ Σ′} {M M′} {ℓ}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ---------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ ref?⟦ ℓ ⟧ M ⊑ ref?⟦ ℓ ⟧ M′

  ⊑-ref✓ : ∀ {Γ Γ′ Σ Σ′} {M M′} {ℓ}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ---------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ ref✓⟦ ℓ ⟧ M ⊑ ref✓⟦ ℓ ⟧ M′

  ⊑-deref : ∀ {Γ Γ′ Σ Σ′} {M M′}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ---------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ ! M ⊑ ! M′

  ⊑-assign : ∀ {Γ Γ′ Σ Σ′} {L L′ M M′}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L ⊑ L′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ---------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L := M ⊑ L′ := M′

  ⊑-assign? : ∀ {Γ Γ′ Σ Σ′} {L L′ M M′}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L ⊑ L′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ---------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L :=? M ⊑ L′ :=? M′

  ⊑-assign✓ : ∀ {Γ Γ′ Σ Σ′} {L L′ M M′}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L ⊑ L′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ---------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ L :=✓ M ⊑ L′ :=✓ M′

  ⊑-prot : ∀ {Γ Γ′ Σ Σ′} {M M′} {ℓ}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      -------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ prot ℓ M ⊑ prot ℓ M′

  ⊑-cast-pc : ∀ {Γ Γ′ Σ Σ′} {M M′} {g}
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      --------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ cast-pc g M ⊑ M′

  ⊑-cast : ∀ {Γ Γ′ Σ Σ′} {A A′ B B′ M M′} {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
    → A ⊑ B → A′ ⊑ B′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩

  ⊑-castl : ∀ {Γ Γ′ Σ Σ′} {A A′ B M M′} {c : Cast A ⇒ B}
    → A ⊑ A′ → B ⊑ A′
    → ∃[ gc′ ] ∃[ pc′ ] Γ′ ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⟨ c ⟩ ⊑ M′

  ⊑-castr : ∀ {Γ Γ′ Σ Σ′} {A A′ B′ M M′} {c′ : Cast A′ ⇒ B′}
    → A ⊑ A′ → A ⊑ B′
    → ∃[ gc ] ∃[ pc ] Γ ; Σ ; gc ; pc ⊢ M ⦂ A
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′
      ------------------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ M′ ⟨ c′ ⟩

  ⊑-err : ∀ {Γ Γ′ Σ Σ′} {M} {e}
      ----------------------------------
    → Γ ; Σ ∣ Γ′ ; Σ′ ⊢ M ⊑ error e
