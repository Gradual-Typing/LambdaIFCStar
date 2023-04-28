module LabelCoercionCalculi.CoercionExp where

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

data ⊢_⇒_ : Label → Label → Set where

  id : ∀ g → ⊢ g ⇒ g

  ↑ : ⊢ l low ⇒ l high

  _! : ∀ ℓ → ⊢ l ℓ ⇒ ⋆

  _??_ : ∀ ℓ (p : BlameLabel) → ⊢ ⋆ ⇒ l ℓ


infixl 8 _∘_  {- syntactic composition -}

data CoercionExp_⇒_ : Label → Label → Set where

  id : ∀ g → CoercionExp g ⇒ g

  _∘_ : ∀ {g₁ g₂ g₃} → CoercionExp g₁ ⇒ g₂ → ⊢ g₂ ⇒ g₃ → CoercionExp g₁ ⇒ g₃

  err : ∀ g₁ g₂ (p : BlameLabel) → CoercionExp g₁ ⇒ g₂


data 𝒱 : ∀ {g₁ g₂} → CoercionExp g₁ ⇒ g₂ → Set where

  id : ∀ {g} → 𝒱 (id g)

  up : 𝒱 ((id _) ∘ ↑)

  inj : ∀ {ℓ} → 𝒱 ((id _) ∘ (ℓ !))

  proj : ∀ {ℓ p} → 𝒱 ((id _) ∘ (ℓ ?? p))

  up-inj : 𝒱 ((id _) ∘ ↑ ∘ (high !))

  proj-up : ∀ {p} → 𝒱 ((id ⋆) ∘ (low ?? p) ∘ ↑)

  proj-inj : ∀ {ℓ p} → 𝒱 ((id ⋆) ∘ (ℓ ?? p) ∘ (ℓ !))

  proj-up-inj : ∀ {p} → 𝒱 ((id ⋆) ∘ (low ?? p) ∘ ↑ ∘ (high !))


infix 2 _⟶_

data _⟶_ : ∀ {g₁ g₂} → CoercionExp g₁ ⇒ g₂ → CoercionExp g₁ ⇒ g₂ → Set where

  ξ : ∀ {g₁ g₂ g₃} {c̅ c̅′ : CoercionExp g₁ ⇒ g₂} {c : ⊢ g₂ ⇒ g₃}
    → c̅ ⟶ c̅′
      ----------------------
    → c̅ ∘ c ⟶ c̅′ ∘ c

  ξ-err : ∀ {p} {g₁ g₂ g₃} {c : ⊢ g₂ ⇒ g₃}
      ------------------------------------------
    → (err g₁ g₂ p) ∘ c ⟶ err g₁ g₃ p

  id : ∀ {g₁ g₂} {c̅ : CoercionExp g₁ ⇒ g₂}
    → 𝒱 c̅
      --------------------------
    → c̅ ∘ (id g₂) ⟶ c̅

  ?-id : ∀ {p} {g ℓ} {c̅ : CoercionExp g ⇒ (l ℓ)}
    → 𝒱 c̅
      ----------------------------------
    → c̅ ∘ (ℓ !) ∘ (ℓ ?? p) ⟶ c̅

  ?-↑ : ∀ {p} {g} {c̅ : CoercionExp g ⇒ (l low)}
    → 𝒱 c̅
      ---------------------------------------
    → c̅ ∘ (low !) ∘ (high ?? p) ⟶ c̅ ∘ ↑

  ?-err : ∀ {p} {g} {c̅ : CoercionExp g ⇒ (l high)}
    → 𝒱 c̅
      -----------------------------------------------
    → c̅ ∘ (high !) ∘ (low ?? p) ⟶ err g (l low) p


data Progress : ∀ {g₁ g₂} → (c̅ : CoercionExp g₁ ⇒ g₂) → Set where

  done : ∀ {g₁ g₂} {c̅ : CoercionExp g₁ ⇒ g₂}
    → 𝒱 c̅
    → Progress c̅

  error : ∀ {p} {g₁ g₂} → Progress (err g₁ g₂ p)

  step : ∀ {g₁ g₂} {c̅ c̅′ : CoercionExp g₁ ⇒ g₂}
    → c̅ ⟶ c̅′
    → Progress c̅


progress : ∀ {g₁ g₂} (c̅ : CoercionExp g₁ ⇒ g₂) → Progress c̅
progress (id g) = done id
progress (c̅ ∘ c) with progress c̅
... | step c̅→c̅′ = step (ξ c̅→c̅′)
... | error = step ξ-err
... | done id with c
progress (_ ∘ c) | done id | id g = step (id id)
progress (_ ∘ c) | done id | ↑ = done up
progress (_ ∘ c) | done id | ℓ ! = done inj
progress (_ ∘ c) | done id | ℓ ?? p = done proj
progress (_ ∘ c) | done up with c
progress (_ ∘ c) | done up | id (l high) = step (id up)
progress (_ ∘ c) | done up | high ! = done up-inj
progress (_ ∘ c) | done inj with c
progress (_ ∘ c) | done inj | id ⋆ = step (id inj)
progress (_ ∘ c) | done (inj {low})  | low ?? p  = step (?-id id)
progress (_ ∘ c) | done (inj {high}) | high ?? p = step (?-id id)
progress (_ ∘ c) | done (inj {low})  | high ?? p = step (?-↑ id)
progress (_ ∘ c) | done (inj {high}) | low ?? p  = step (?-err id)
progress (_ ∘ c) | done proj with c
progress (_ ∘ c) | done proj | id (l ℓ) = step (id proj)
progress (_ ∘ c) | done proj | ℓ ! = done proj-inj
progress (_ ∘ c) | done proj | ↑ = done proj-up
progress (_ ∘ c) | done up-inj with c
progress (_ ∘ c) | done up-inj | id ⋆ = step (id up-inj)
progress (_ ∘ c) | done up-inj | low ?? p = step (?-err up)
progress (_ ∘ c) | done up-inj | high ?? p = step (?-id up)
progress (_ ∘ c) | done proj-up with c
progress (_ ∘ c) | done proj-up | id _ = step (id proj-up)
progress (_ ∘ c) | done proj-up | high ! = done proj-up-inj
progress (_ ∘ c) | done proj-inj with c
progress (_ ∘ c) | done proj-inj | id ⋆ = step (id proj-inj)
progress (_ ∘ c) | done (proj-inj {low}) | low ?? p = step (?-id proj)
progress (_ ∘ c) | done (proj-inj {high}) | low ?? p = step (?-err proj)
progress (_ ∘ c) | done (proj-inj {low}) | high ?? p = step (?-↑ proj)
progress (_ ∘ c) | done (proj-inj {high}) | high ?? p = step (?-id proj)
progress (_ ∘ c) | done proj-up-inj with c
progress (_ ∘ c) | done proj-up-inj | id ⋆ = step (id proj-up-inj)
progress (_ ∘ c) | done proj-up-inj | low ?? p = step (?-err proj-up)
progress (_ ∘ c) | done proj-up-inj | high ?? p = step (?-id proj-up)
progress (err g₁ g₂ p) = error


data ⊢_⊑_⦂_;_ : ∀ {g₁ g₁′ g₂ g₂′}
  → (CoercionExp g₁ ⇒ g₂) → (CoercionExp g₁′ ⇒ g₂′)
  → g₁ ⊑ₗ g₁′ → g₂ ⊑ₗ g₂′ → Set where

  ⊑-id : ∀ {g g′}
    → (g⊑g′ : g ⊑ₗ g′)
      ---------------------------------
    → ⊢ id g ⊑ id g′ ⦂ g⊑g′ ; g⊑g′

  ⊑-cast : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
             {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
             {c : ⊢ g₂ ⇒ g₃} {c′ : ⊢ g₂′ ⇒ g₃′} {g₁⊑g₁′} {g₂⊑g₂′}
    → ⊢ c̅ ⊑ c̅′ ⦂ g₁⊑g₁′ ; g₂⊑g₂′
    → (g₃⊑g₃′ : g₃ ⊑ₗ g₃′)
      -------------------------------------------
    → ⊢ c̅ ∘ c ⊑ c̅′ ∘ c′ ⦂ g₁⊑g₁′ ; g₃⊑g₃′

  ⊑-castl : ∀ {g₁ g₁′ g₂ g₂′ g₃}
              {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
              {c : ⊢ g₂ ⇒ g₃} {g₁⊑g₁′} {g₂⊑g₂′}
    → ⊢ c̅ ⊑ c̅′ ⦂ g₁⊑g₁′ ; g₂⊑g₂′
    → (g₃⊑g₂′ : g₃ ⊑ₗ g₂′)
      -------------------------------------------
    → ⊢ c̅ ∘ c ⊑ c̅′ ⦂ g₁⊑g₁′ ; g₃⊑g₂′

  ⊑-castr : ∀ {g₁ g₁′ g₂ g₂′ g₃′}
              {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
              {c′ : ⊢ g₂′ ⇒ g₃′} {g₁⊑g₁′} {g₂⊑g₂′}
    → ⊢ c̅ ⊑ c̅′ ⦂ g₁⊑g₁′ ; g₂⊑g₂′
    → (g₂⊑g₃′ : g₂ ⊑ₗ g₃′)
      -------------------------------------------
    → ⊢ c̅ ⊑ c̅′ ∘ c′ ⦂ g₁⊑g₁′ ; g₂⊑g₃′

  ⊑-err : ∀ {g₁ g₁′ g₂ g₂′} {c̅ : CoercionExp g₁ ⇒ g₂} {p}
    → (g₁⊑g₁′ : g₁ ⊑ₗ g₁′)
    → (g₂⊑g₂′ : g₂ ⊑ₗ g₂′)
      ---------------------------------
    → ⊢ c̅ ⊑ err g₁′ g₂′ p ⦂ g₁⊑g₁′ ; g₂⊑g₂′
