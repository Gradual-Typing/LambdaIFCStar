module LabelCoercionCalculi.C where

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

data LabelExp : Label → Set where

  l : (ℓ : StaticLabel) → LabelExp (l ℓ)

  _⟨_⟩ : ∀ {g₁ g₂} → LabelExp g₁ → ⊢ g₁ ⇒ g₂ → LabelExp g₂

  bl : ∀ {g} (p : BlameLabel) → LabelExp g

data LabelVal : ∀ {g} → LabelExp g → Set where

  v-l : ∀ {ℓ} → LabelVal (l ℓ)

  v-! : ∀ {ℓ} → LabelVal (l ℓ ⟨ ℓ ! ⟩)

infix 2 _⟶_

data _⟶_ : ∀ {g} → LabelExp g → LabelExp g → Set where

  ξ : ∀ {g₁ g₂} {e e′ : LabelExp g₁} {c : ⊢ g₁ ⇒ g₂}
    → e ⟶ e′
      ----------------------
    → e ⟨ c ⟩ ⟶ e′ ⟨ c ⟩

  ξ-bl : ∀ {p} {g₁ g₂} {c : ⊢ g₁ ⇒ g₂} → (bl p) ⟨ c ⟩ ⟶ bl p

  id : ∀ {g} {e : LabelExp g}
    → LabelVal e
      --------------------------
    → e ⟨ id g ⟩ ⟶ e

  ↑ : l low ⟨ ↑ ⟩ ⟶ l high

  seq : ∀ {g₁ g₂ g₃} {e : LabelExp g₁} {c : ⊢ g₁ ⇒ g₂} {d : ⊢ g₂ ⇒ g₃}
    → LabelVal e
      -----------------------------------
    → e ⟨ seq c d ⟩ ⟶ (e ⟨ c ⟩) ⟨ d ⟩

  ?-id : ∀ {p} {ℓ} {e : LabelExp (l ℓ)}
    → LabelVal e
      ----------------------------------
    → (e ⟨ ℓ ! ⟩) ⟨ ℓ ?? p ⟩ ⟶ l ℓ

  ?-↑ : ∀ {p} {e}
    → LabelVal e
      ---------------------------------------
    → (e ⟨ low ! ⟩) ⟨ high ?? p ⟩ ⟶ l high

  ?-bl : ∀ {p} {e}
    → LabelVal e
      ---------------------------------------
    → (e ⟨ high ! ⟩) ⟨ low ?? p ⟩ ⟶ bl p

  bl : ∀ {p} {g₁ g₂} {e : LabelExp g₁}
    → LabelVal e
      -------------------------
    → e ⟨ ⊥_ {g₁} {g₂} p ⟩ ⟶ bl {g₂} p

data Progress : ∀ {g} → (e : LabelExp g) → Set where

  done : ∀ {g} {e : LabelExp g}
    → LabelVal e
    → Progress {g} e

  blame : ∀ {p} {g} → Progress (bl {g} p)

  step : ∀ {g} {e e′ : LabelExp g}
    → e ⟶ e′
    → Progress e

progress : ∀ {g} (e : LabelExp g) → Progress e
progress {l ℓ} (l ℓ) = done v-l
progress {g} (e ⟨ c ⟩) with progress e
... | step e→e′ = step (ξ e→e′)
... | blame = step ξ-bl
... | done v-l with c
...   | id _ = step (id v-l)
...   | ℓ ! = done v-!
...   | ↑ = step ↑
...   | seq c d = step (seq v-l)
...   | ⊥ p = step (bl v-l)
progress {g} (e ⟨ c ⟩) | done (v-! {ℓ₁}) with c
... | id _ = step (id v-!)
... | seq c d = step (seq v-!)
... | ⊥ p = step (bl v-!)
... | ℓ₂ ?? p with ℓ₁ | ℓ₂
...   | low | low = step (?-id v-l)
...   | high | high = step (?-id v-l)
...   | low | high = step (?-↑ v-l)
...   | high | low = step (?-bl v-l)
progress {g} (bl p) = blame
