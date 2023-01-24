module ExamplePrograms.Simulation.WrongAnn1 where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang


{- less precise -}
M =
  `let ƛ⟦ low ⟧ ` Bool of ⋆ ˙ (` 0) ∶ ` Bool of ⋆ at pos 0 of low `in
  (` 0 · $ false of high at pos 1)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢lam (⊢ann (⊢var refl) ≲-refl))
     (⊢app (⊢var refl) ⊢const (≲-ty ≾-⋆r ≲ᵣ-refl) ≾-refl ≾-refl)

{- more precise -}
M′ =
  `let ƛ⟦ low ⟧ ` Bool of ⋆ ˙ (` 0) ∶ ` Bool of l low at pos 0 of low `in
  (` 0 · $ false of high at pos 1)

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l low
⊢M′ = ⊢let (⊢lam (⊢ann (⊢var refl) (≲-ty ≾-⋆l ≲ᵣ-refl)))
      (⊢app (⊢var refl) ⊢const (≲-ty ≾-⋆r ≲ᵣ-refl) ≾-refl ≾-refl)
