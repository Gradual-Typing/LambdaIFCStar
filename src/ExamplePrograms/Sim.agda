module ExamplePrograms.Sim where

open import Data.Unit
open import Data.List
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils
open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang
open import CC.CCStatics renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ⟦_⟧_˙_of_ to lam⟦_⟧_˙_of_; !_ to *_)
open import CC.Compile renaming (compile to 𝒞; compilation-preserves-type to 𝒞-pres)
open import CC.Reduction
open import CC.TypeSafety
open import CC.BigStep
open import Memory.Heap CCTerm Value

open import Simulator.AST
open import Simulator.CheckPrecision
open import CC.Interp


M₁ =
  `let (($ true of low) ∶ ` Bool of ⋆ at pos 0) `in
  `let ((` 0) ∶ ` Bool of ⋆ at pos 0) `in
    (` 0)

⊢M₁ : [] ; l low ⊢ᴳ M₁ ⦂ ` Bool of ⋆
⊢M₁ = ⊢let (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)) (⊢let (⊢ann (⊢var refl) ≲-refl) (⊢var refl))

𝒞M₁  = 𝒞 M₁ ⊢M₁
⊢𝒞M₁ = 𝒞-pres M₁ ⊢M₁

t₁ = to-ast 𝒞M₁ ⊢𝒞M₁

M₁′ =
  `let (($ true of low) ∶ ` Bool of l high at pos 0) `in
  `let ((` 0) ∶ ` Bool of ⋆ at pos 0) `in
    (` 0)

⊢M₁′ : [] ; l low ⊢ᴳ M₁′ ⦂ ` Bool of ⋆
⊢M₁′ =
  ⊢let (⊢ann ⊢const (≲-ty (≾-l l≼h) ≲-ι)) (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r ≲-ι)) (⊢var refl))

𝒞M₁′  = 𝒞 M₁′ ⊢M₁′
⊢𝒞M₁′ = 𝒞-pres M₁′ ⊢M₁′

t₁′ = to-ast 𝒞M₁′ ⊢𝒞M₁′

b₁ = check-⊑? t₁ t₁′

N₁ = let ⟨ N , _ , 𝒞M₁↠N₁ ⟩      = interp 𝒞M₁ ⊢𝒞M₁ 42 in N
𝒞M₁↠N₁ = let ⟨ N , _ , 𝒞M₁↠N₁ ⟩ = interp 𝒞M₁ ⊢𝒞M₁ 42 in 𝒞M₁↠N₁
⊢N₁ : [] ; ∅ ; l low ; low ⊢ N₁ ⦂ ` Bool of ⋆
⊢N₁ = let ⟨ Σ , ⊢N₁ , ⊢μ ⟩ = multi-preserve ⊢𝒞M₁ 𝒞M₁↠N₁ in ⊢N₁
N₁′ = let ⟨ N , _ , 𝒞M₁′↠N₁′ ⟩ = interp 𝒞M₁′ ⊢𝒞M₁′ 42 in N
𝒞M₁′↠N₁′ = let ⟨ N , _ , 𝒞M₁′↠N₁′ ⟩ = interp 𝒞M₁′ ⊢𝒞M₁′ 42 in 𝒞M₁′↠N₁′
⊢N₁′ : [] ; ∅ ; l low ; low ⊢ N₁′ ⦂ ` Bool of ⋆
⊢N₁′ = let ⟨ Σ , ⊢N₁′ , ⊢μ ⟩ = multi-preserve ⊢𝒞M₁′ 𝒞M₁′↠N₁′ in ⊢N₁′

b₂ = check-⊑? (to-ast N₁ ⊢N₁) (to-ast N₁′ ⊢N₁′)
