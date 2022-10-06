module Examples where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Types
open import BlameLabels
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module StaticExamples where

open import SurfaceLang

_ : Term
_ = (ƛ[ low ] (` Bool of ⋆ ) ˙ (` 0) of high) · (` 0) at pos 0

postulate
  publish : Term
  ⊢publish : [] ; l low ⊢ᴳ publish ⦂ [ l low ] ` Bool of l low ⇒ (` Unit of l low) of l low

Mₕ : Term
Mₕ =
  -- publish --
  `let publish ∶ [ l low ] (` Bool of l low) ⇒ (` Unit of l low) of l low `in
  -- flip --
  `let ƛ[ low ] ` Bool of l high ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low ∶
       [ l low ] (` Bool of l high) ⇒ (` Bool of l high) of l low `in
  -- result --
  `let $ true of high ∶ ` Bool of l high `in
  (` 2 · (` 1 · ` 0 at pos 1) at pos 2)

-- ⊢Mₕ : [] ; l low ⊢ᴳ Mₕ ⦂ ` Unit of l low
-- ⊢Mₕ = ⊢let ⊢publish
--        (⊢let (⊢lam (⊢if (⊢var refl) ⊢const ⊢const refl))
--          (⊢let ⊢const
--            (⊢app (⊢var refl) (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl) {!!} ≾-refl ≾-refl)))

Mₗ : Term
Mₗ =
  -- publish --
  `let publish ∶ [ l low ] (` Bool of l low) ⇒ (` Unit of l low) of l low `in
  -- flip --
  `let ƛ[ low ] ` Bool of l high ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low ∶
       [ l low ] (` Bool of l high) ⇒ (` Bool of l low) of l low `in
  -- result --
  `let $ true of high ∶ ` Bool of l high `in
  (` 2 · (` 1 · ` 0 at pos 1) at pos 2)

-- ⊢Mₗ : [] ; l low ⊢ᴳ Mₗ ⦂ ` Unit of l low
-- ⊢Mₗ = ⊢let ⊢publish
--        (⊢let (⊢lam (⊢if (⊢var {!!}) ⊢const ⊢const refl))
--          (⊢let ⊢const
--            (⊢app (⊢var refl) (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl) ≲-refl ≾-refl ≾-refl)))

M : Term
M =
  -- publish --
  `let publish ∶ [ l low ] (` Bool of l low) ⇒ (` Unit of l low) of l low `in
  -- dumb --
  `let ƛ[ low ] ` Bool of l high ˙ $ false of low of low ∶
       [ l low ] (` Bool of l high) ⇒ (` Bool of l low) of l low `in
  -- result --
  `let $ true of high ∶ ` Bool of l high `in
  (` 2 · (` 1 · ` 0 at pos 1) at pos 2)

⊢M : [] ; l low ⊢ᴳ M ⦂ ` Unit of l low
⊢M = ⊢let ⊢publish
       (⊢let (⊢lam ⊢const)
         (⊢let ⊢const
           (⊢app (⊢var refl) (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl) ≲-refl ≾-refl ≾-refl)))

{- Explicit type annotation -}
_ : Term
_ = `let ($ true of high) ∶ ` Bool of ⋆ at pos 0 ∶ ` Bool of ⋆ `in (` 0)


module DynamicExamples where

open import SurfaceLang
  renaming (`_ to `ᴳ_;
            $_of_ to $ᴳ_of_;
            ƛ[_]_˙_of_ to ƛᴳ[_]_˙_of_;
            !_ to !ᴳ_)
open import CC renaming (Term to CCTerm)
