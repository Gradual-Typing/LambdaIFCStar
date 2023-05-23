module LabelCoercionCalculus.Coercions where

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


NotProj : ∀ (g₁ g₂ : Label) → Set
NotProj g₁ g₂ = Concrete g₂ → Concrete g₁


coerce-nproj : ∀ (g₁ g₂ : Label) → g₁ ≾ g₂ → NotProj g₁ g₂ → ⊢ g₁ ⇒ g₂
coerce-nproj ⋆ ⋆ _ _ = id ⋆
coerce-nproj (l ℓ) ⋆ ≾-⋆r _  = ℓ !
coerce-nproj ⋆ (l ℓ) ≾-⋆l np = case np l of λ where ()
coerce-nproj (l low)  (l low)  (≾-l l≼l) _ = id (l low)
coerce-nproj (l low)  (l high) (≾-l l≼h) _ = ↑
coerce-nproj (l high) (l high) (≾-l h≼h) _ = id (l high)

coerce : ∀ (g₁ g₂ : Label) → g₁ ≾ g₂ → BlameLabel → ⊢ g₁ ⇒ g₂
coerce ⋆ (l ℓ)  g₁≾g₂ p = ℓ ?? p  {- requires a blame label when projecting -}
coerce ⋆     ⋆  g₁≾g₂ p = coerce-nproj ⋆ ⋆ g₁≾g₂ (λ x → x)
coerce (l ℓ) g₂ g₁≾g₂ p = coerce-nproj (l ℓ) g₂ g₁≾g₂ λ _ → l
