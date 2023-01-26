module ExamplePrograms.Simulation.WrongAnn2 where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M =
  `let ($ true of low) ∶ ` Bool of ⋆ at pos 0 `in
  `let (` 0)           ∶ ` Bool of ⋆ at pos 1      `in
    ((ƛ⟦ low ⟧ ` Bool of l low ˙ $ tt of low of low) · ` 0 at pos 2)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Unit of l low
⊢M =
   ⊢let (⊢ann ⊢const (≲-ty ≾-⋆r ≲ᵣ-refl))
  (⊢let (⊢ann (⊢var refl) ≲-refl)
    (⊢app (⊢lam ⊢const) (⊢var refl) (≲-ty ≾-⋆l ≲ᵣ-refl) ≾-refl ≾-refl))

{- more precise -}
M′ =
  `let ($ true of low) ∶ ` Bool of l high at pos 0 `in
  `let (` 0)           ∶ ` Bool of ⋆ at pos 1      `in
    ((ƛ⟦ low ⟧ ` Bool of l low ˙ $ tt of low of low) · ` 0 at pos 2)
⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Unit of l low
⊢M′ =
   ⊢let (⊢ann ⊢const (≲-ty (≾-l l≼h) ≲ᵣ-refl))
  (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r ≲ᵣ-refl))
    (⊢app (⊢lam ⊢const) (⊢var refl) (≲-ty ≾-⋆l ≲ᵣ-refl) ≾-refl ≾-refl))
