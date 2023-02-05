module ExamplePrograms.Simulation.RefCast1 where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M =
  `let (ref⟦ high ⟧ $ true of low at pos 1) ∶ Ref (` Bool of ⋆) of ⋆ at pos 0 `in
  `let (` 0) := $ false of high at pos 2 `in
  (! ((` 1) ∶ Ref (` Bool of ⋆) of ⋆ at pos 3))

{- more precise -}
M′ =
  `let (ref⟦ high ⟧ $ true of low at pos 1) ∶ Ref (` Bool of l high) of ⋆ at pos 0 `in
  `let (` 0) := $ false of high at pos 2 `in
  (! ((` 1) ∶ Ref (` Bool of l high) of ⋆ at pos 3))


⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲ᵣ-refl) (≾-l l≼h)) (≲-ty ≾-⋆r (≲-ref (≲-ty ≾-⋆r ≲-ι) (≲-ty ≾-⋆l ≲-ι))))
      (⊢let (⊢assign (⊢var refl) ⊢const (≲-ty ≾-⋆r ≲-ι) ≾-⋆l ≾-⋆r)
      (⊢deref (⊢ann (⊢var refl) ≲-refl)))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of ⋆
⊢M′ = ⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲ᵣ-refl) (≾-l l≼h)) (≲-ty ≾-⋆r ≲ᵣ-refl))
      (⊢let (⊢assign (⊢var refl) ⊢const ≲-refl ≾-⋆l (≾-l l≼h))
      (⊢deref (⊢ann (⊢var refl) ≲-refl)))
