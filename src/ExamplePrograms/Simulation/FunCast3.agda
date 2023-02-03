module ExamplePrograms.Simulation.FunCast3 where

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
  `let (` 0) ∶ ⟦ ⋆ ⟧ (` Bool of ⋆) ⇒ (` Bool of ⋆) of ⋆ at pos 0 `in
  (((` 0) ∶ ⟦ ⋆ ⟧ (` Bool of l low) ⇒ (` Bool of l high) of ⋆ at pos 2) · $ false of low at pos 1)

{- more precise -}
M′ =
  `let ƛ⟦ high ⟧ ` Bool of l high ˙ ` 0 of low `in
  `let (` 0) ∶ ⟦ ⋆ ⟧ (` Bool of l low) ⇒ (` Bool of l high) of ⋆ at pos 0 `in
  (((` 0) ∶ ⟦ ⋆ ⟧ (` Bool of l low) ⇒ (` Bool of l high) of l low at pos 2) · $ false of low at pos 1)


⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢lam (⊢var refl))
    (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl (≲-ty ≾-⋆l ≲-ι))))
       (⊢app (⊢ann (⊢var refl) (≲-ty ≾-refl (≲-fun ≾-⋆r (≲-ty ≾-⋆r ≲-ι) (≲-ty ≾-⋆l ≲-ι))))
             ⊢const (≲-ty ≾-refl ≲-ι) ≾-⋆l ≾-⋆r))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l high
⊢M′ = ⊢let (⊢lam (⊢var refl))
     (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r (≲-fun ≾-⋆l (≲-ty (≾-l l≼h) ≲-ι) ≲-refl)))
       (⊢app (⊢ann (⊢var refl) (≲-ty ≾-⋆l ≲ᵣ-refl)) ⊢const (≲-ty ≾-refl ≲-ι) ≾-⋆r ≾-⋆r))
