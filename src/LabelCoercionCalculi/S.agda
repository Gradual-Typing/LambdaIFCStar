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

_⨟_ : ∀ {g₁ g₂ g₃} (c : ⊢ g₁ ⇒ g₂) (d : ⊢ g₂ ⇒ g₃)
  → Canonical c → Canonical d
  → ⊢ g₁ ⇒ g₃
((id g) ⨟ d) id _ = d
(c ⨟ (id g)) _ id = c
((⊥ p) ⨟ d) bot _ = ⊥ p
(c ⨟ (⊥ p)) _ bot = ⊥ p
(↑ ⨟ (high !)) up inj = ↑ ; high !
((ℓ₁ !) ⨟ (ℓ₂ ?? p)) inj proj with ℓ₁ | ℓ₂
... | low  | low  = id (l low)
... | high | high = id (l high)
... | low  | high = ↑
... | high | low  = ⊥ p
((ℓ !) ⨟ (low ?? p ; ↑)) inj proj-up with ℓ
... | low = ↑
... | high = ⊥ p
((ℓ₁ !) ⨟ (ℓ₂ ?? p ; ℓ₂ !)) inj proj-inj with ℓ₁ | ℓ₂
... | low  | low  = low !
... | high | high = high !
... | low  | high = ↑ ; high !
... | high | low  = ⊥ p
((ℓ !) ⨟ (low ?? p ; ↑ ; high !)) inj proj-up-inj with ℓ
... | low  = ↑ ; high !
... | high = ⊥ p
((low ?? p) ⨟ ↑) proj up = low ?? p ; ↑
((ℓ ?? p) ⨟ (ℓ !)) proj inj = ℓ ?? p ; ℓ !
((low ?? p) ⨟ (↑ ; high !)) proj up-inj = low ?? p ; ↑ ; high !
((↑ ; high !) ⨟ (ℓ ?? p)) up-inj proj with ℓ
... | low  = ⊥ p
... | high = ↑
((↑ ; high !) ⨟ (low ?? p ; ↑)) up-inj proj-up = ⊥ p
((↑ ; high !) ⨟ (ℓ ?? p ; ℓ !)) up-inj proj-inj with ℓ
... | low  = ⊥ p
... | high = ↑ ; high !
((↑ ; high !) ⨟ (low ?? p ; ↑ ; high !)) up-inj proj-up-inj = ⊥ p
((low ?? p ; ↑) ⨟ (high !)) proj-up inj = low ?? p ; ↑ ; high !
((ℓ₁ ?? p ; ℓ₁ !) ⨟ (ℓ₂ ?? q)) proj-inj proj with ℓ₁ | ℓ₂
... | low  | low  = low ?? p
... | high | high = high ?? p
... | low  | high = low ?? p ; ↑
... | high | low  = ⊥ q
((ℓ ?? p ; ℓ !) ⨟ (low ?? q ; ↑)) proj-inj proj-up with ℓ
... | low  = low ?? p ; ↑
... | high = ⊥ q
((ℓ₁ ?? p ; ℓ₁ !) ⨟ (ℓ₂ ?? q ; ℓ₂ !)) proj-inj proj-inj with ℓ₁ | ℓ₂
... | low  | low  = low ?? p ; low !
... | high | high = high ?? p ; high !
... | low  | high = low ?? p ; ↑ ; high !
... | high | low  = ⊥ q
((ℓ ?? p ; ℓ !) ⨟ (low ?? q ; ↑ ; high !)) proj-inj proj-up-inj with ℓ
... | low  = low ?? p ; ↑ ; high !
... | high = ⊥ q
((low ?? p ; ↑ ; high !) ⨟ (ℓ ?? q)) proj-up-inj proj with ℓ
... | low  = ⊥ q
... | high = low ?? p ; ↑
((low ?? p ; ↑ ; high !) ⨟ (low ?? q ; ↑)) proj-up-inj proj-up = ⊥ q
((low ?? p ; ↑ ; high !) ⨟ (ℓ ?? q ; ℓ !)) proj-up-inj proj-inj with ℓ
... | low  = ⊥ q
... | high = low ?? p ; ↑ ; high !
((low ?? p ; ↑ ; high !) ⨟ (low ?? q ; ↑ ; high !)) proj-up-inj proj-up-inj = ⊥ q
