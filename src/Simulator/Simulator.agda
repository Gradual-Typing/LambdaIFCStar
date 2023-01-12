module Simulator.Simulator where

open import Data.Unit
open import Data.Nat
open import Data.List
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Maybe
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang
open import Surface.Precision
open import CC.CCStatics renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ⟦_⟧_˙_of_ to lam⟦_⟧_˙_of_; !_ to *_)
open import CC.Compile renaming (compile to 𝒞; compilation-preserves-type to 𝒞-pres)
open import CC.Reduction
open import CC.TypeSafety
open import CC.BigStep
open import Memory.Heap CCTerm Value

open import Simulator.AST
open import Simulator.CheckPrecision


magic-num = 42

sim-helper : ∀ {Σ gc A} M μ
  → [] ; Σ ; gc ; low ⊢ M ⦂ A
  → Σ ⊢ μ → (t : AST) → (k : ℕ)
    ------------------------------------------
  → Maybe CCTerm
sim-helper M μ ⊢M ⊢μ t 0 =
  if (check-⊑? (to-ast M ⊢M) t) then (just M) else nothing
sim-helper M μ ⊢M ⊢μ t (suc k-1) =
  if (check-⊑? (to-ast M ⊢M) t) then (just M)
    else
    (case progress low M ⊢M μ ⊢μ of λ where
      (step {N} {μ′} M→N) →
        let ⟨ Σ′ , Σ′⊇Σ , ⊢N , ⊢μ′ ⟩ = preserve ⊢M ⊢μ (low≾ _) M→N in
        sim-helper N μ′ ⊢N ⊢μ′ t k-1
      (done v)      {- M is value already -} → nothing
      (err E-error) {- M is an error -}      → nothing)

simulator : ∀ {A A′} (M M′ : CCTerm)
  → [] ; ∅ ; l low ; low ⊢ M  ⦂ A
  → [] ; ∅ ; l low ; low ⊢ M′ ⦂ A′
  → 𝔹
simulator M M′ ⊢M ⊢M′ =
  case sim-helper M ∅ ⊢M ⊢μ-nil (to-ast M′ ⊢M′) magic-num of λ where
  nothing  → false
  (just N) → true
