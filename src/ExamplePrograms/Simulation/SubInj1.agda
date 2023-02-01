module ExamplePrograms.Simulation.SubInj1 where

open import Data.List using ([])
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M =
  `let ($ true of low) ∶ ` Bool of ⋆ at pos 0 `in
  `let (` 0)           ∶ ` Bool of ⋆ at pos 1 `in
  (` 0)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M =
  ⊢let (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
  (⊢let (⊢ann (⊢var refl) ≲-refl)
    (⊢var refl))

{- more precise -}
M′ =
  `let ($ true of low) ∶ ` Bool of l high at pos 0 `in
  `let (` 0)           ∶ ` Bool of ⋆      at pos 1 `in
  (` 0)

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of ⋆
⊢M′ =
  ⊢let (⊢ann ⊢const (≲-ty (≾-l l≼h) ≲-ι))
  (⊢let (⊢ann (⊢var refl) (≲-ty ≾-⋆r ≲-ι))
    (⊢var refl))

{- less precise AST
let-bind

   (cast (const true low (` Bool of l low)) (` Bool of l low) (` Bool of ⋆) (` Bool of ⋆))

(let-bind (var 0 (` Bool of ⋆)) (var 0 (` Bool of ⋆))
 (` Bool of ⋆))
(` Bool of ⋆)
-}

{- more precise AST
let-bind

   (const true low (` Bool of l high))

(let-bind
 (cast (var 0 (` Bool of l high)) (` Bool of l high) (` Bool of ⋆)
  (` Bool of ⋆))
 (var 0 (` Bool of ⋆)) (` Bool of ⋆))
(` Bool of ⋆)
-}
