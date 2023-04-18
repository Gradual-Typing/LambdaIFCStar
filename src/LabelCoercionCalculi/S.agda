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
((ℓ !) ⨟ (low ?? p ; ↑ ; high !)) inj proj-up-inj = {!!}
((ℓ ?? p) ⨟ d) proj cd = {!!}
((↑ ; high !) ⨟ d) up-inj cd = {!!}
((low ?? _ ; ↑) ⨟ d) proj-up cd = {!!}
((ℓ ?? _ ; ℓ !) ⨟ d) proj-inj cd = {!!}
((low ?? _ ; ↑ ; high !) ⨟ d) proj-up-inj cd = {!!}
