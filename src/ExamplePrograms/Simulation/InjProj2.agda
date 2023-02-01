module ExamplePrograms.Simulation.InjProj2 where

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
  ((` 0) ∶ ` Bool of l low at pos 2)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of l low
⊢M =
  ⊢let (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
  (⊢let (⊢ann (⊢var refl) ≲-refl)
    (⊢ann (⊢var refl) (≲-ty ≾-⋆l ≲-ι)))

{- more precise -}
M′ =
  `let ($ true of low) ∶ ` Bool of l low at pos 0 `in
  `let (` 0)           ∶ ` Bool of ⋆      at pos 1 `in
  ((` 0) ∶ ` Bool of l low at pos 2)

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l low
⊢M′ =
  ⊢let (⊢ann ⊢const (≲-ty ≾-refl ≲-ι))
  (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r ≲-ι))
    (⊢ann (⊢var refl) (≲-ty ≾-⋆l ≲-ι)))
