{- Label coercion in normal form -}

module LabelCoercionCalculi.S where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import LabelCoercionCalculi.Coercion

data Canonical : ∀ {g₁ g₂} → ⊢ g₁ ⇒ g₂ → Set where

  id : ∀ {g} → Canonical (id (g))

  up : Canonical ↑

  inj : ∀ {ℓ} → Canonical (ℓ !)

  proj : ∀ {p} {ℓ} → Canonical (ℓ ?? p)

  bot : ∀ {p} {g₁ g₂} → Canonical (⊥_ {g₁} {g₂} p)

  up-inj : Canonical  (↑ ; high !)

  proj-up : ∀ {p} → Canonical (low ?? p ; ↑)

  proj-inj : ∀ {p ℓ} → Canonical ((ℓ ?? p) ; (ℓ !))

  proj-up-inj : ∀ {p} → Canonical ((low ?? p) ; ↑ ; (high !))

{-
    id(g) ; c = c            c ; id(g) = c

    ⊥ᵖ    ; c = ⊥ᵖ           c ; ⊥ᵖ    = ⊥ᵖ

    ℓ    ! ; ℓ    ?ᵖ = id(ℓ)
    low  ! ; high ?ᵖ = ↑
    high ! ; low  ?ᵖ = ⊥ᵖ

    (c₁ ; c₂) ; c₃ = c₁ ; (c₂ ; c₃)
-}

_⨟_ : ∀ {g₁ g₂ g₃} (c₁ : ⊢ g₁ ⇒ g₂) (c₂ : ⊢ g₂ ⇒ g₃)
  → Canonical c₁
  → Canonical c₂
  → Σ[ d ∈ ⊢ g₁ ⇒ g₃ ] (Canonical d)
((id g) ⨟ d) id cd = ⟨ d , cd ⟩
(c ⨟ (id g)) cc id = ⟨ c , cc ⟩
((⊥ p) ⨟ d) bot _ = ⟨ ⊥ p , bot ⟩
(c ⨟ (⊥ p)) _ bot = ⟨ ⊥ p , bot ⟩
(↑ ⨟ (high !)) up inj = ⟨ ↑ ; high ! , up-inj ⟩
((ℓ₁ !) ⨟ (ℓ₂ ?? p)) inj proj with ℓ₁ | ℓ₂
... | low  | low  = ⟨ id (l low) , id ⟩
... | high | high = ⟨ id (l high) , id ⟩
... | low  | high = ⟨ ↑ , up ⟩
... | high | low  = ⟨ ⊥ p , bot ⟩
((ℓ !) ⨟ (low ?? p ; ↑)) inj proj-up with ℓ
... | low = ⟨ ↑ , up ⟩
... | high = ⟨ ⊥ p , bot ⟩
((ℓ₁ !) ⨟ (ℓ₂ ?? p ; ℓ₂ !)) inj proj-inj with ℓ₁ | ℓ₂
... | low  | low  = ⟨ low ! , inj ⟩
... | high | high = ⟨ high ! , inj ⟩
... | low  | high = ⟨ ↑ ; high ! , up-inj ⟩
... | high | low  = ⟨ ⊥ p , bot ⟩
((ℓ !) ⨟ (low ?? p ; ↑ ; high !)) inj proj-up-inj with ℓ
... | low  = ⟨ ↑ ; high ! , up-inj ⟩
... | high = ⟨ ⊥ p , bot ⟩
((low ?? p) ⨟ ↑) proj up = ⟨ low ?? p ; ↑ , proj-up ⟩
((ℓ ?? p) ⨟ (ℓ !)) proj inj = ⟨ ℓ ?? p ; ℓ ! , proj-inj ⟩
((low ?? p) ⨟ (↑ ; high !)) proj up-inj = ⟨ low ?? p ; ↑ ; high ! , proj-up-inj ⟩
((↑ ; high !) ⨟ (ℓ ?? p)) up-inj proj with ℓ
... | low  = ⟨ ⊥ p , bot ⟩
... | high = ⟨ ↑ , up ⟩
((↑ ; high !) ⨟ (low ?? p ; ↑)) up-inj proj-up = ⟨ ⊥ p , bot ⟩
((↑ ; high !) ⨟ (ℓ ?? p ; ℓ !)) up-inj proj-inj with ℓ
... | low  = ⟨ ⊥ p , bot ⟩
... | high = ⟨ ↑ ; high ! , up-inj ⟩
((↑ ; high !) ⨟ (low ?? p ; ↑ ; high !)) up-inj proj-up-inj = ⟨ ⊥ p , bot ⟩
((low ?? p ; ↑) ⨟ (high !)) proj-up inj = ⟨ low ?? p ; ↑ ; high ! , proj-up-inj ⟩
((ℓ₁ ?? p ; ℓ₁ !) ⨟ (ℓ₂ ?? q)) proj-inj proj with ℓ₁ | ℓ₂
... | low  | low  = ⟨ low ?? p , proj ⟩
... | high | high = ⟨ high ?? p , proj ⟩
... | low  | high = ⟨ low ?? p ; ↑ , proj-up ⟩
... | high | low  = ⟨ ⊥ q , bot ⟩
((ℓ ?? p ; ℓ !) ⨟ (low ?? q ; ↑)) proj-inj proj-up with ℓ
... | low  = ⟨ low ?? p ; ↑ , proj-up ⟩
... | high = ⟨ ⊥ q , bot ⟩
((ℓ₁ ?? p ; ℓ₁ !) ⨟ (ℓ₂ ?? q ; ℓ₂ !)) proj-inj proj-inj with ℓ₁ | ℓ₂
... | low  | low  = ⟨ low ?? p ; low ! , proj-inj ⟩
... | high | high = ⟨ high ?? p ; high ! , proj-inj ⟩
... | low  | high = ⟨ low ?? p ; ↑ ; high ! , proj-up-inj ⟩
... | high | low  = ⟨ ⊥ q , bot ⟩
((ℓ ?? p ; ℓ !) ⨟ (low ?? q ; ↑ ; high !)) proj-inj proj-up-inj with ℓ
... | low  = ⟨ low ?? p ; ↑ ; high ! , proj-up-inj ⟩
... | high = ⟨ ⊥ q , bot ⟩
((low ?? p ; ↑ ; high !) ⨟ (ℓ ?? q)) proj-up-inj proj with ℓ
... | low  = ⟨ ⊥ q , bot ⟩
... | high = ⟨ low ?? p ; ↑ , proj-up ⟩
((low ?? p ; ↑ ; high !) ⨟ (low ?? q ; ↑)) proj-up-inj proj-up = ⟨ ⊥ q , bot ⟩
((low ?? p ; ↑ ; high !) ⨟ (ℓ ?? q ; ℓ !)) proj-up-inj proj-inj with ℓ
... | low  = ⟨ ⊥ q , bot ⟩
... | high = ⟨ low ?? p ; ↑ ; high ! , proj-up-inj ⟩
((low ?? p ; ↑ ; high !) ⨟ (low ?? q ; ↑ ; high !)) proj-up-inj proj-up-inj = ⟨ ⊥ q , bot ⟩
