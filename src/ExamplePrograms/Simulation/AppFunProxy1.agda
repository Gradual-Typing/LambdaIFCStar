module ExamplePrograms.Simulation.AppFunProxy1 where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang


{- less precise -}
M =
  `let ƛ⟦ low ⟧ ` Bool of l low ˙ ` 0 of low `in
  `let (` 0) ∶ ⟦ ⋆ ⟧ (` Bool of l low) ⇒ (` Bool of l low) of ⋆ at pos 0 `in
  (` 0 · $ false of low at pos 1)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢lam (⊢var refl))
    (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl ≲-refl)))
       (⊢app (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆r))

{- more precise -}
M′ =
  `let ƛ⟦ low ⟧ ` Bool of l low ˙ ` 0 of low `in
  `let (` 0) ∶ ⟦ l low ⟧ (` Bool of l low) ⇒ (` Bool of l low) of l low at pos 0 `in
  (` 0 · $ false of low at pos 1)

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l low
⊢M′ = ⊢let (⊢lam (⊢var refl))
     (⊢let (⊢ann (⊢var refl) ≲-refl)
       (⊢app (⊢var refl) ⊢const ≲-refl ≾-refl ≾-refl))
