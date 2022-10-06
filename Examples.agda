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

{- Explicit type annotation: -}
_ : Term
_ =
  `let ($ true of high) ∶ ` Bool of ⋆ at pos 0 `in
  (` 0)

postulate
  publish : Term
  ⊢publish : [] ; l low ⊢ᴳ publish ⦂ [ l low ] ` Bool of l low ⇒ (` Unit of l low) of l low

{- Statically accepted: -}
N : Term
N =
  -- publish : 𝔹 of low → ⊤
  `let publish `in
  -- dumb    : 𝔹 of high → 𝔹 of low
  `let ƛ[ low ] ` Bool of l high ˙ $ false of low of low `in
  -- input   : 𝔹 of high
  `let $ true of high `in
  -- result  : 𝔹 of low
  `let ` 1 {- dumb -} · ` 0 {- input -} at pos 0 `in
    (` 3 {- publish -} · ` 0 {- result -} at pos 1)

⊢N : [] ; l low ⊢ᴳ N ⦂ ` Unit of l low
⊢N =
  ⊢let ⊢publish
  (⊢let (⊢lam ⊢const)
  (⊢let ⊢const
  (⊢let (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl)
    (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl))))

{- Statically rejected: -}
M : Term
M =
  -- publish : 𝔹 of low → ⊤
  `let publish `in
  -- flip    : 𝔹 of high → 𝔹 of high
  `let ƛ[ low ] ` Bool of l high ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low `in
  -- input   : 𝔹 of high
  `let $ true of high `in
  -- result  : 𝔹 of high
  `let ` 1 {- flip -} · ` 0 {- input -} at pos 1 `in
    (` 3 {- publish -} · ` 0 {- result -} at pos 2)

-- ⊢M : [] ; l low ⊢ᴳ M ⦂ ` Unit of l low
-- ⊢M =
--   ⊢let ⊢publish
--   (⊢let (⊢lam (⊢if (⊢var {!!}) ⊢const ⊢const refl))
--   (⊢let ⊢const
--   (⊢let (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl)
--     (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl))))

{- Give `result` an extra annotation: -}
M* : Term
M* =
  -- publish : 𝔹 of low → ⊤
  `let publish `in
  -- flip    : 𝔹 of high → 𝔹 of high
  `let ƛ[ low ] ` Bool of l high ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low `in
  -- input   : 𝔹 of high
  `let $ true of high `in
  -- result  : 𝔹 of ⋆
  `let (` 1 {- flip -} · ` 0 {- input -} at pos 1) ∶ ` Bool of ⋆ at pos 2 `in
    (` 3 {- publish -} · ` 0 {- result -} at pos 3)

⊢M* : [] ; l low ⊢ᴳ M* ⦂ ` Unit of l low
⊢M* =
  ⊢let ⊢publish
  (⊢let (⊢lam (⊢if (⊢var refl) ⊢const ⊢const refl))
  (⊢let ⊢const
  (⊢let (⊢ann (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl) (≲-ty ≾-⋆r ≲ᵣ-refl))
    (⊢app (⊢var refl) (⊢var refl) (≲-ty ≾-⋆l ≲ᵣ-refl) ≾-refl ≾-refl))))

{- Alternatively we can annotation function `flip`: -}
M*′ : Term
M*′ =
  -- publish : 𝔹 of low → ⊤
  `let publish `in
  -- flip    : 𝔹 of high → 𝔹 of ⋆
  `let (ƛ[ low ] ` Bool of l high ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low) ∶
       [ l low ] (` Bool of l high) ⇒ (` Bool of ⋆) of l low at pos 1 `in
  -- input   : 𝔹 of high
  `let $ true of high `in
  -- result  : 𝔹 of ⋆
  `let ` 1 {- flip -} · ` 0 {- input -} at pos 2 `in
    (` 3 {- publish -} · ` 0 {- result -} at pos 3)

⊢M*′ : [] ; l low ⊢ᴳ M*′ ⦂ ` Unit of l low
⊢M*′ =
  ⊢let ⊢publish
  (⊢let (⊢ann (⊢lam (⊢if (⊢var refl) ⊢const ⊢const refl)) (≲-ty ≾-refl (≲-fun ≾-refl ≲-refl (≲-ty ≾-⋆r ≲ᵣ-refl))))
  (⊢let ⊢const
  (⊢let (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl)
    (⊢app (⊢var refl) (⊢var refl) (≲-ty ≾-⋆l ≲ᵣ-refl) ≾-refl ≾-refl))))


module DynamicExamples where

open import SurfaceLang
  renaming (`_ to `ᴳ_;
            $_of_ to $ᴳ_of_;
            ƛ[_]_˙_of_ to ƛᴳ[_]_˙_of_;
            !_ to !ᴳ_)
open import CC renaming (Term to CCTerm)
