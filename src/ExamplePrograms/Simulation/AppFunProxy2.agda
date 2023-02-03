module ExamplePrograms.Simulation.AppFunProxy2 where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang


{- less precise -}
M =
  `let ƛ⟦ high ⟧ ` Bool of ⋆ ˙ ` 0 of low `in
  `let (` 0) ∶ ⟦ ⋆ ⟧ (` Bool of ⋆) ⇒ (` Bool of l low) of ⋆ at pos 0 `in
  (` 0 · $ false of low at pos 1)

{- more precise -}
M′ =
  `let ƛ⟦ high ⟧ ` Bool of l low ˙ ` 0 of low `in
  `let (` 0) ∶ ⟦ l low ⟧ (` Bool of l low) ⇒ (` Bool of l low) of ⋆ at pos 0 `in
  (` 0 · $ false of low at pos 1)


⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢lam (⊢var refl))
    (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl (≲-ty ≾-⋆l ≲-ι))))
       (⊢app (⊢var refl) ⊢const (≲-ty ≾-⋆r ≲-ι) ≾-refl ≾-⋆r))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of ⋆
⊢M′ = ⊢let (⊢lam (⊢var refl))
     (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r (≲-fun (≾-l l≼h) ≲-refl ≲-refl)))
       (⊢app (⊢var refl) ⊢const ≲-refl ≾-⋆l ≾-refl))
