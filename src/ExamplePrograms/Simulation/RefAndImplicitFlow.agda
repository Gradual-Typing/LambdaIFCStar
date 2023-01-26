module ExamplePrograms.Simulation.RefAndImplicitFlow where

{-
  This example is about "references and implicit flows".
  The example is adapted from Section 2 of Toro et al. 2018,
  which is in turn adapted from Austin and Flanagan 2009.
-}

open import Data.List using ([])
open import Data.Unit
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang

{- less precise -}
M =
  `let {- x = -} $ true of high `in
  `let {- y = -} (ref⟦ high ⟧ $ true of low at pos 1) ∶ Ref (` Bool of ⋆) of ⋆ at pos 0          `in
  `let {- z = -} (ref⟦ high ⟧ $ true of low at pos 3) ∶ Ref (` Bool of l high) of l low at pos 2 `in
  `let {- _ = -} if (` 2) then (` 1) := $ false of low at pos 5 else $ tt of low at pos 4        `in
  `let {- _ = -} if (! (` 2)) then (` 1) := $ false of low at pos 7 else $ tt of low at pos 6    `in
  (! (` 2))

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Bool of l high
⊢M =
  ⊢let ⊢const
  (⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h)) (≲-ty ≾-⋆r (≲-ref (≲-ty ≾-⋆r ≲-ι) (≲-ty ≾-⋆l ≲-ι))))
  (⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h)) ≲-refl)
  (⊢let (⊢if (⊢var refl) (⊢assign (⊢var refl) ⊢const (≲-ty ≾-⋆r ≲-ι) ≾-refl ≾-⋆r) ⊢const refl)
  (⊢let (⊢if (⊢deref (⊢var refl)) (⊢assign (⊢var refl) ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h) ≾-⋆l) ⊢const refl)
  (⊢deref (⊢var refl))))))

{- more precise -}
M′ =
  `let {- x = -} $ true of high `in
  `let {- y = -} (ref⟦ high ⟧ $ true of low at pos 1) ∶ Ref (` Bool of l high) of l low at pos 0 `in
  `let {- z = -} (ref⟦ high ⟧ $ true of low at pos 3) ∶ Ref (` Bool of l high) of l low at pos 2 `in
  `let {- _ = -} if (` 2) then (` 1) := $ false of low at pos 5 else $ tt of low at pos 4        `in
  `let {- _ = -} if (! (` 2)) then (` 1) := $ false of low at pos 7 else $ tt of low at pos 6    `in
  (! (` 2))

⊢M′ : [] ; l low ⊢ᴳ M′ ⦂ ` Bool of l high
⊢M′ =
  ⊢let ⊢const
  (⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h)) ≲-refl)
  (⊢let (⊢ann (⊢ref ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h)) ≲-refl)
  (⊢let (⊢if (⊢var refl) (⊢assign (⊢var refl) ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h) ≾-refl) ⊢const refl)
  (⊢let (⊢if (⊢deref (⊢var refl)) (⊢assign (⊢var refl) ⊢const (≲-ty (≾-l l≼h) ≲-ι) (≾-l l≼h) ≾-refl) ⊢const refl)
  (⊢deref (⊢var refl))))))

-- make sure that M and M′ are indeed related
open import Surface.Precision

_ : M ⊑ˢ M′
_ =
  ⊑ˢ-let ⊑ˢ-const
  (⊑ˢ-let (⊑ˢ-ann (⊑ˢ-ref ⊑ˢ-const) (⊑-ty ⋆⊑ (⊑-ref (⊑-ty ⋆⊑ ⊑-ι))))
  (⊑ˢ-let (⊑ˢ-ann (⊑ˢ-ref ⊑ˢ-const) (⊑-ty l⊑l (⊑-ref (⊑-ty l⊑l ⊑-ι))))
  (⊑ˢ-let (⊑ˢ-if ⊑ˢ-var (⊑ˢ-assign ⊑ˢ-var ⊑ˢ-const) ⊑ˢ-const)
  (⊑ˢ-let (⊑ˢ-if (⊑ˢ-deref ⊑ˢ-var) (⊑ˢ-assign ⊑ˢ-var ⊑ˢ-const) ⊑ˢ-const)
  (⊑ˢ-deref ⊑ˢ-var)))))
