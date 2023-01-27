module ExamplePrograms.Simulation.SubInj1 where

open import Data.List using ([])
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang


{- less precise -}
M =
  `let ($ true of low) ∶ ` Bool of ⋆ at pos 0 `in
  `let (` 0)           ∶ ` Bool of ⋆ at pos 1 `in
  (` 0)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M =
  ⊢let (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
  (⊢let (⊢ann (⊢var refl) ≲-refl)
    (⊢var refl))

{- more precise -}
M′ =
  `let ($ true of low) ∶ ` Bool of l high at pos 0 `in
  `let (` 0)           ∶ ` Bool of ⋆      at pos 1 `in
  (` 0)

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of ⋆
⊢M′ =
  ⊢let (⊢ann ⊢const (≲-ty (≾-l l≼h) ≲-ι))
  (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r ≲-ι))
    (⊢var refl))
