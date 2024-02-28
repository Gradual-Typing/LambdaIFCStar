module Dyn.HeapSecure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Dyn.Syntax
open import Dyn.Values
open import Dyn.BigStep
open import Dyn.Erasure
open import Memory.Heap Term Value


{- Related heaps under high PC -}
heap-relate : ∀ {M V μ μ′}
  → μ ∣ high ⊢ M ⇓ V ∣ μ′
    ----------------------------------------
  → erase-μ μ ≡ erase-μ μ′
heap-relate (⇓-val v) = refl
heap-relate (⇓-app L⇓ƛN M⇓V N[V]⇓W)
  rewrite heap-relate L⇓ƛN | heap-relate M⇓V | heap-relate N[V]⇓W = refl
heap-relate (⇓-if-true L⇓true M⇓V)
  rewrite heap-relate L⇓true | heap-relate M⇓V = refl
heap-relate (⇓-if-false L⇓false N⇓V)
  rewrite heap-relate L⇓false | heap-relate N⇓V = refl
heap-relate (⇓-ref? M⇓V fresh h≼h {- ℓ ≡ high -})
  rewrite heap-relate M⇓V = refl
heap-relate (⇓-deref M⇓a eq) = heap-relate M⇓a
heap-relate (⇓-assign? L⇓a M⇓V h≼h)
  rewrite heap-relate L⇓a | heap-relate M⇓V = refl

Secure : Heap → Set
Secure μ = ∀ n V v → lookup-μ μ (a⟦ high ⟧ n) ≡ just (V & v) → erase V ≡ ●

postulate
  ⇓-pres-sec : ∀ {μ₁ μ₂ pc M V}
    → Secure μ₁
    → μ₁ ∣ pc ⊢ M ⇓ V ∣ μ₂
    → Secure μ₂
-- ⇓-pres-secure sec M⇓V = {!!}
