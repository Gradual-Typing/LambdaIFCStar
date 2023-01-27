module ExamplePrograms.Simulation.Values where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M = ($ true of low) ∶ ` Bool of ⋆ at pos 0

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M = ⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)

{- more precise -}
M′ = ($ true of low) ∶ ` Bool of l low at pos 0

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l low
⊢M′ = ⊢ann ⊢const ≲-refl
