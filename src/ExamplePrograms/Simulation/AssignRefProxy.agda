module ExamplePrograms.Simulation.AssignRefProxy where

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- Create a reference proxy and then assign to it, but no NSU on the more precise side -}

{- less precise -}
M =
  `let (ref⟦ high ⟧ $ true of low at pos 0) ∶ Ref (` Bool of ⋆) of ⋆ at pos 1 `in
  `let if $ true of high
       then (` 0) := $ false of low at pos 3
       else (` 0) := $ true  of low at pos 4
       at pos 5 `in
  (! (` 1))

{- more precise -}
M′ =
  `let (ref⟦ high ⟧ $ true of low at pos 0) ∶ Ref (` Bool of l high) of ⋆ at pos 1 `in
  `let if $ true of high
       then (` 0) := $ false of low at pos 3
       else (` 0) := $ true  of low at pos 4
       at pos 5 `in
  (! (` 1))


⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of ⋆
⊢M =
  ⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h)) (≲-ty ≾-⋆r (≲-ref (≲-ty ≾-⋆r ≲-ι) (≲-ty ≾-⋆l ≲-ι))))
  (⊢let (⊢if ⊢const
             (⊢assign (⊢var refl) ⊢const (≲-ty ≾-⋆r ≲-ι) ≾-⋆l ≾-⋆r)
             (⊢assign (⊢var refl) ⊢const (≲-ty ≾-⋆r ≲-ι) ≾-⋆l ≾-⋆r) refl)
  (⊢deref (⊢var refl)))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of ⋆
⊢M′ =
  ⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h)) (≲-ty ≾-⋆r ≲ᵣ-refl))
  (⊢let (⊢if ⊢const
             (⊢assign (⊢var refl) ⊢const (≲-ty (≾-l l≼h) ≲-ι) ≾-⋆l ≾-refl)
             (⊢assign (⊢var refl) ⊢const (≲-ty (≾-l l≼h) ≲-ι) ≾-⋆l ≾-refl) refl)
  (⊢deref (⊢var refl)))
