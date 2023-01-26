module ExamplePrograms.Simulation.DerefRefProxy where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M =
  `let ref⟦ low ⟧ $ true of low at pos 0      `in
  `let (` 0) ∶ Ref (` Bool of ⋆) of ⋆ at pos 1 `in
  (! (` 0))

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
     (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r (≲-ref (≲-ty ≾-⋆r ≲-ι) (≲-ty ≾-⋆l ≲-ι))))
       (⊢deref (⊢var refl)))

{- more precise -}
M′ =
  `let ref⟦ low ⟧ $ true of low at pos 0      `in
  `let (` 0) ∶ Ref (` Bool of l low) of l high at pos 1 `in
  (! (` 0))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l high
⊢M′ = ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
     (⊢let (⊢ann (⊢var refl) (≲-ty (≾-l l≼h) ≲ᵣ-refl))
       (⊢deref (⊢var refl)))
