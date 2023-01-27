module ExamplePrograms.Simulation.IfFalseAssign where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang


{- less precise -}
M =
  `let $ false of high `in
  `let ref⟦ high ⟧ (($ true of high) ∶ ` Bool of ⋆ at pos 3) at pos 0 `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low                at pos 2

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Unit of l high
⊢M =
  ⊢let ⊢const
  (⊢let (⊢ref (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)) (≲-ty ≾-⋆l ≲-ι) (≾-l l≼h))
    (⊢if (⊢var refl)
         (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
         ⊢const refl))

{- more precise -}
M′ =
  `let $ false of high `in
  `let ref⟦ high ⟧ $ true of high at pos 0 `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low                at pos 2

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Unit of l high
⊢M′ =
  ⊢let ⊢const
    (⊢let (⊢ref ⊢const ≲-refl (≾-l l≼h))
      (⊢if (⊢var refl)
           (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
           ⊢const refl))
