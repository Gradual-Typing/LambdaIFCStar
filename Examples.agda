module Examples where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Utils
open import Types
open import BlameLabels
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module TypeExamples where

_ : Type
_ =  [ ⋆ ] (` Bool of ⋆) ⇒ (` Bool of l high) of l low

_ : Type
_ = Ref (` Unit of ⋆) of l high


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
open import CC renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ[_]_˙_of_ to lam[_]_˙_of_; !_ to deref)

open import Compile

publish-cc : CCTerm
publish-cc = compile publish ⊢publish

M*⇒ : CCTerm
M*⇒ = compile M*′ ⊢M*′

open import Reduction
open import Heap
open import TypeBasedCast

{- Note the 2 casts inserted: -}
_ :
  let c~₁ = ~-ty ~ₗ-refl (~-fun ~ₗ-refl ~-refl (~-ty ~⋆ ~ᵣ-refl)) in
  let c₁ = cast ([ l low ] (` Bool of l high) ⇒ (` Bool of l high) of l low)
                ([ l low ] (` Bool of l high) ⇒ (` Bool of ⋆     ) of l low)
                (pos 1) c~₁ in
  let c~₂ = ~-ty ⋆~ ~ᵣ-refl in
  let c₂ = cast (` Bool of ⋆) (` Bool of l low) (pos 3) c~₂ in
  M*⇒ ≡
  `let publish-cc
  (`let (lam[ low ] ` Bool of l high ˙ if (var 0) (` Bool of l low) (const false of low) (const true of low) of low ⟨ c₁ ⟩)
  (`let (const true of high)
  (`let (var 1 · var 0)
  (var 3 · var 0 ⟨ c₂ ⟩))))
_ = refl

_ : M*⇒ ∣ ∅ ∣ low —↠ error (blame (pos 3)) ∣ ∅
_ = {!!}
