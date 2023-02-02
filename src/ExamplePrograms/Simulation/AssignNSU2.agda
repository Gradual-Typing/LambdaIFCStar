module ExamplePrograms.Simulation.AssignNSU2 where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M =
  `let (ref⟦ low ⟧ $ true of low at pos 0) ∶ Ref (` Bool of l low) of ⋆ at pos 1 `in
  `let if (($ true of high) ∶ ` Bool of ⋆ at pos 2)
       then (` 0) := $ false of low at pos 3
       else (` 0) := $ true  of low at pos 4
       at pos 5 `in
  (! (` 1))

{- more precise -}
M′ =
  `let (ref⟦ low ⟧ $ true of low at pos 0) ∶ Ref (` Bool of l low) of l low at pos 1 `in
  `let if (($ true of high) ∶ ` Bool of ⋆ at pos 2)
       then (` 0) := $ false of low at pos 3
       else (` 0) := $ true  of low at pos 4
       at pos 5 `in
  (! (` 1))


⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M =
  ⊢let (⊢ann (⊢ref ⊢const ≲-refl ≾-refl) (≲-ty ≾-⋆r ≲ᵣ-refl))
  (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-⋆l ≾-⋆l)
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-⋆l ≾-⋆l) refl)
  (⊢deref (⊢var refl)))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l low
⊢M′ =
  ⊢let (⊢ann (⊢ref ⊢const ≲-refl ≾-refl) (≲-ty ≾-refl ≲ᵣ-refl))
  (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
             (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l) refl)
  (⊢deref (⊢var refl)))
