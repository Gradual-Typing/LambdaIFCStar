module ExamplePrograms.Simulation.SubInj where

open import Data.Unit
open import Data.List
open import Data.Maybe
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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


M =
  `let (($ true of low) ∶ ` Bool of ⋆ at pos 0) `in
  `let ((` 0) ∶ ` Bool of ⋆ at pos 0) `in
    (` 0)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)) (⊢let (⊢ann (⊢var refl) ≲-refl) (⊢var refl))

M′ =
  `let (($ true of low) ∶ ` Bool of l high at pos 0) `in
  `let ((` 0) ∶ ` Bool of ⋆ at pos 0) `in
    (` 0)

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of ⋆
⊢M′ =
  ⊢let (⊢ann ⊢const (≲-ty (≾-l l≼h) ≲-ι))
       (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r ≲-ι)) (⊢var refl))


open import Simulator.Simulator

b = simulator M M′ ⊢M ⊢M′
