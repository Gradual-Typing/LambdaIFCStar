module LabelCoercionCalculi.Precision where

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
open import LabelCoercionCalculi.CoercionExp


infix 4 ⊢_⊑_

data ⊢_⊑_ : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CoercionExp g₁ ⇒ g₂) (c̅′ : CoercionExp g₁′ ⇒ g₂′) → Set where

  ⊑-id : ∀ {g g′}
    → (g⊑g′ : g ⊑ₗ g′)
      ---------------------------------
    → ⊢ id g ⊑ id g′

  ⊑-cast : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
             {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
             {c : ⊢ g₂ ⇒ g₃} {c′ : ⊢ g₂′ ⇒ g₃′}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₃′ {- c ⊑ c′ -}
      -------------------------------------------
    → ⊢ c̅ ⨾ c ⊑ c̅′ ⨾ c′

  ⊑-castl : ∀ {g₁ g₁′ g₂ g₂′ g₃}
              {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
              {c : ⊢ g₂ ⇒ g₃}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₂′  {- c ⊑ g₂′ -}
      -------------------------------------------
    → ⊢ c̅ ⨾ c ⊑ c̅′

  ⊑-castr : ∀ {g₁ g₁′ g₂ g₂′ g₃′}
              {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
              {c′ : ⊢ g₂′ ⇒ g₃′}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₂ ⊑ₗ g₃′  {- g₂ ⊑ c′ -}
      -------------------------------------------
    → ⊢ c̅ ⊑ c̅′ ⨾ c′

  ⊑-⊥ : ∀ {g₁ g₁′ g₂ g₂′} {c̅ : CoercionExp g₁ ⇒ g₂} {p}
    → g₁ ⊑ₗ g₁′
    → g₂ ⊑ₗ g₂′
      ---------------------------------
    → ⊢ c̅ ⊑ ⊥ g₁′ g₂′ p

prec→⊑ : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CoercionExp g₁ ⇒ g₂) (c̅′ : CoercionExp g₁′ ⇒ g₂′)
  → ⊢ c̅ ⊑ c̅′
  → ((g₁ ⊑ₗ g₁′) × (g₂ ⊑ₗ g₂′))
prec→⊑ (id g) (id g′) (⊑-id g⊑g′) = ⟨ g⊑g′ , g⊑g′ ⟩
prec→⊑ (c̅ ⨾ c) (c̅′ ⨾ c′) (⊑-cast c̅⊑c̅′ _ g₂⊑g₂′) =
  case prec→⊑ c̅ c̅′ c̅⊑c̅′ of λ where
  ⟨ g₁⊑g₁′ , _ ⟩ → ⟨ g₁⊑g₁′ , g₂⊑g₂′ ⟩
prec→⊑ (c̅ ⨾ c) c̅′ (⊑-castl c̅⊑c̅′ g₂⊑g₂′ g₃⊑g₂′) =
  case prec→⊑ c̅ c̅′ c̅⊑c̅′ of λ where
  ⟨ g₁⊑g₁′ , _ ⟩ → ⟨ g₁⊑g₁′ , g₃⊑g₂′ ⟩
prec→⊑ c̅ (c̅′ ⨾ c′) (⊑-castr c̅⊑c̅′ g₂⊑g₂′ g₂⊑g₃′) =
  case prec→⊑ c̅ c̅′ c̅⊑c̅′ of λ where
  ⟨ g₁⊑g₁′ , _ ⟩ → ⟨ g₁⊑g₁′ , g₂⊑g₃′ ⟩
prec→⊑ c̅ (⊥ _ _ _) (⊑-⊥ g₁⊑g₁′ g₂⊑g₂′) = ⟨ g₁⊑g₁′ , g₂⊑g₂′ ⟩
