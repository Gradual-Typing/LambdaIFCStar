module ExamplePrograms.Simulation.InjProj1 where

open import Data.List using ([])
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang


{- less precise -}
M = ((($ true of low) ∶ ` Bool of l high at pos 0)
                      ∶ ` Bool of ⋆ at pos 1)
                      ∶ ` Bool of l low at pos 2


⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of l low
⊢M = ⊢ann (⊢ann (⊢ann ⊢const (≲-ty (≾-l l≼h) ≲-ι)) (≲-ty ≾-⋆r ≲-ι)) (≲-ty ≾-⋆l ≲-ι)


{- more precise -}
M′ = ((($ true of low) ∶ ` Bool of l low at pos 0)
                       ∶ ` Bool of ⋆ at pos 1)
                       ∶ ` Bool of l low at pos 2

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l low
⊢M′ = ⊢ann (⊢ann (⊢ann ⊢const (≲-ty ≾-refl ≲-ι)) (≲-ty ≾-⋆r ≲-ι)) (≲-ty ≾-⋆l ≲-ι)

{-
  high ⊑<: low
  ----------------------------------------- CastL
  true of low ⟨ high ⇒ ⋆ ⟩ ⊑? true of low     ⋆ ⊑ low     ⋆ ⊑ ⋆
  ----------------------------------------------------------------- CastR
  true of low ⟨ high ⇒ ⋆ ⟩ ⊑? true of low ⟨ low ⇒ ⋆ ⟩

  high ⊑ ⋆    ⋆ ⊑ ⋆
  ----------------------------------------------------------------- CastL
  true of low ⟨ high ⇒ ⋆ ⟩ ⊑? true of low ⟨ low ⇒ ⋆ ⟩

cast

  (cast (const true low (` Bool of l high)) (` Bool of l high) (` Bool of ⋆) (` Bool of ⋆))

(` Bool of ⋆) (` Bool of l low) (` Bool of l low)

cast

  (cast (const true low (` Bool of l low)) (` Bool of l low) (` Bool of ⋆) (` Bool of ⋆))

(` Bool of ⋆) (` Bool of l low) (` Bool of l low)
-}
