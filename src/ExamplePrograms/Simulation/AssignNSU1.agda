module ExamplePrograms.Simulation.AssignNSU1 where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M =
  `let ref⟦ low ⟧ $ true of low at pos 0 `in
  `let if (($ true of high) ∶ ` Bool of ⋆ at pos 1)
       then (` 0) := $ false of low at pos 2
       else (` 0) := $ true  of low at pos 3
       at pos 4 `in
  (! (` 1))

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of l low
⊢M =
  ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
  (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l) refl)
    (⊢deref (⊢var refl)))

{- more precise -}
M′ =
  `let ref⟦ low ⟧ $ true of low at pos 0 `in
  `let if (($ true of high) ∶ ` Bool of ⋆ at pos 1)
       then (` 0) := $ false of low at pos 2
       else (` 0) := $ true  of low at pos 3
       at pos 4 `in
  (! (` 1))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l low
⊢M′ =
  ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
  (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l) refl)
    (⊢deref (⊢var refl)))
