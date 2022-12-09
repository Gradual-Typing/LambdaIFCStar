module Interp where

open import Data.Nat
open import Data.Unit using (⊤) renaming (tt to unit)
open import Data.List
-- open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; cong₂; cong-app)
open import Function using (case_of_)

open import Utils
open import Types
open import BlameLabels
open import TypeBasedCast
open import Heap
open import HeapTyping
open import CC
open import Reduction
open import TypeSafety

interp : ∀ {Σ gc A} pc M → [] ; Σ ; gc ; pc ⊢ M ⦂ A → ∀ μ → Σ ⊢ μ → (k : ℕ)
  → ∃[ N ] ∃[ μ′ ] (M ∣ μ ∣ pc —↠ N ∣ μ′)
interp pc M ⊢M μ ⊢μ 0                   = ⟨ M , μ , _ ∣ _ ∣ _ ∎ ⟩
interp pc M (⊢sub ⊢M A<:B) μ ⊢μ k       = interp pc M ⊢M μ ⊢μ k
interp pc M (⊢sub-pc ⊢M gc<:gc′) μ ⊢μ k = interp pc M ⊢M μ ⊢μ k
interp pc M ⊢M μ ⊢μ (suc k-1) =
  case progress pc M ⊢M μ ⊢μ of λ where
  (step {N} {μ′} M→N) →
    ⟨ N , μ′ , M ∣ μ ∣ pc —→⟨ M→N ⟩ N ∣ μ′ ∣ pc ∎ ⟩
  (done v) →
    ⟨ M , μ , _ ∣ _ ∣ _ ∎ ⟩
  (err E-error) →
    ⟨ error _ , μ , _ ∣ _ ∣ _ ∎ ⟩
