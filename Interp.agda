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

interpret : ∀ {Σ gc A} pc M → [] ; Σ ; gc ; pc ⊢ M ⦂ A → ∀ μ → Σ ⊢ μ → l pc ≾ gc → (k : ℕ)
  → ∃[ N ] ∃[ μ′ ] (M ∣ μ ∣ pc —↠ N ∣ μ′)
interpret pc M ⊢M μ ⊢μ pc≾gc 0                   = ⟨ M , μ , _ ∣ _ ∣ _ ∎ ⟩
interpret pc M (⊢sub ⊢M A<:B) μ ⊢μ pc≾gc k       = interpret pc M ⊢M μ ⊢μ pc≾gc k
interpret pc M (⊢sub-pc ⊢M gc<:gc′) μ ⊢μ pc≾gc k = interpret pc M ⊢M μ ⊢μ (≾-<: pc≾gc gc<:gc′) k
interpret pc M ⊢M μ ⊢μ pc≾gc (suc k-1) =
  case progress pc M ⊢M μ ⊢μ of λ where
  (step {M′} {μ′} M→M′) →
    let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ pc≾gc M→M′ in
    case interpret pc M′ ⊢M′ μ′ ⊢μ′ pc≾gc k-1 of λ where
    ⟨ M″ , μ″ , M′↠M″ ⟩ →
      ⟨ M″ , μ″ , M ∣ μ ∣ pc —→⟨ M→M′ ⟩ M′↠M″ ⟩
  (done v) →
    ⟨ M , μ , _ ∣ _ ∣ _ ∎ ⟩
  (err E-error) →
    ⟨ error _ , μ , _ ∣ _ ∣ _ ∎ ⟩

{- When running the interpreter, we always start with PC = low and μ = ∅ -}
interp : ∀ {gc A} M → [] ; ∅ ; gc ; low ⊢ M ⦂ A → (k : ℕ) → _
interp {gc} M ⊢M k = interpret low M ⊢M ∅ ⊢μ-nil (low≾ gc) k
