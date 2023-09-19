module CC2.CastSubtyping where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common.Utils
open import CoercionExpr.SecurityLevel
open import CC2.Statics
open import CC2.CastReduction


{- Cast to value justifies label subtyping -}
cast-≼ : ∀ {Γ Σ gc ℓv} {S T ℓ₁ ℓ₂} {V W} {c : Cast S of l ℓ₁ ⇒ T of l ℓ₂}
  → Value V
  → Γ ; Σ ; gc ; ℓv ⊢ V ⇐ S of l ℓ₁
  → V ⟨ c ⟩ —↠ W
  → Value W
    --------------------------------------
  → ℓ₁ ≼ ℓ₂
cast-≼ v ⊢V ↠W w = {!!}

