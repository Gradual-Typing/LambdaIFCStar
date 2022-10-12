module Example3 where

open import Data.Unit
open import Data.List
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Types
open import BlameLabels
open import SurfaceLang
open import CC renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ[_]_˙_of_ to lam[_]_˙_of_; !_ to deref)
open import Compile
open import Reduction
open import BigStep
open import Heap
open import TypeBasedCast

{- Fully static. Input (branch condition) is `true` in M₁ `false` in M₂ -}
M₁ M₂ : Term
M₁ =
  `let ($ true of high) `in
  `let (ref[ high ] $ true of high at pos 0) `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low at pos 2
M₂ =
  `let ($ false of high) `in
  `let (ref[ high ] $ true of high at pos 0) `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low at pos 2

{- They're both well-typed, of course -}
⊢M₁ : [] ; l low ⊢ᴳ M₁ ⦂ ` Unit of l high
⊢M₁ =
  ⊢let ⊢const
    (⊢let (⊢ref ⊢const ≲-refl (≾-l l≼h))
      (⊢if (⊢var refl)
           (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
           ⊢const refl))
⊢M₂ : [] ; l low ⊢ᴳ M₂ ⦂ ` Unit of l high
⊢M₂ =
  ⊢let ⊢const
    (⊢let (⊢ref ⊢const ≲-refl (≾-l l≼h))
      (⊢if (⊢var refl)
           (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
           ⊢const refl))

{- Both evaluate to `tt` -}
M₁⇓tt :
  let μ = ⟨ [] , ⟨ 0 , (const false of high) & V-const ⟩ ∷ ⟨ 0 , (const true of high) & V-const ⟩ ∷ [] ⟩ in
    ∅ ∣ low ⊢ compile M₁ ⊢M₁ ⇓ const tt of high ∣ μ
M₁⇓tt = ⇓-let (⇓-val V-const)
        (⇓-let (⇓-ref (⇓-val V-const) refl)
        (⇓-if-true (⇓-val V-const) (⇓-assign (⇓-val V-addr) (⇓-val V-const))))

M₂⇓tt :
  let μ = ⟨ [] , ⟨ 0 , (const true of high) & V-const ⟩ ∷ [] ⟩ in
    ∅ ∣ low ⊢ compile M₂ ⊢M₂ ⇓ const tt of high ∣ μ
M₂⇓tt = ⇓-let (⇓-val V-const)
        (⇓-let (⇓-ref (⇓-val V-const) refl)
        (⇓-if-false (⇓-val V-const) (⇓-val V-const)))

{- More dynamic. Input (branch condition) is `true` in M*₁ `false` in M*₂ -}
M*₁ M*₂ : Term
M*₁ =
  `let ($ true of high) `in
  `let (ref[ high ] ($ true of high) ∶ ` Bool of ⋆ at pos 3 at pos 0) `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low at pos 2
M*₂ =
  `let ($ false of high) `in
  `let (ref[ high ] ($ true of high) ∶ ` Bool of ⋆ at pos 3 at pos 0) `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low at pos 2

{- They're again both well-typed -}
⊢M*₁ : [] ; l low ⊢ᴳ M*₁ ⦂ ` Unit of l high
⊢M*₁ =
  ⊢let ⊢const
    (⊢let (⊢ref (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)) (≲-ty ≾-⋆l ≲-ι) (≾-l l≼h))
      (⊢if (⊢var refl)
           (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
           ⊢const refl))
⊢M*₂ : [] ; l low ⊢ᴳ M*₂ ⦂ ` Unit of l high
⊢M*₂ =
  ⊢let ⊢const
    (⊢let (⊢ref (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)) (≲-ty ≾-⋆l ≲-ι) (≾-l l≼h))
      (⊢if (⊢var refl)
           (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
           ⊢const refl))

M*₁⇒ =
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 3) (~-ty ~⋆ ~-ι) in
  let c₂ = cast (` Bool of ⋆) (` Bool of l high) (pos 0) (~-ty ⋆~ ~-ι) in
  `let (const true of high)
       (`let (ref[ high ] ((const true of high ⟨ c₁ ⟩) ⟨ c₂ ⟩))
             (if (var 1) (` Unit of l low) (var 0 := (const false of high)) (const tt of low)))

_ : compile M*₁ ⊢M*₁ ≡ M*₁⇒
_ = refl

{- Evaluate to `tt` again -}
M*₁⇓tt :
  let μ = ⟨ [] , ⟨ 0 , (const false of high) & V-const ⟩ ∷ ⟨ 0 , (const true of high) & V-const ⟩ ∷ [] ⟩ in
    ∅ ∣ low ⊢ compile M*₁ ⊢M*₁ ⇓ const tt of high ∣ μ
M*₁⇓tt = ⇓-let (⇓-val V-const)
         (⇓-let (⇓-ref (⇓-cast (A-base-proj _) (⇓-val (V-cast V-const (I-base-inj _))) (cast-base-proj h≼h) (⇓-val V-const)) refl)
         (⇓-if-true (⇓-val V-const) (⇓-assign (⇓-val V-addr) (⇓-val V-const))))

M*₂⇓tt :
  let μ = ⟨ [] , ⟨ 0 , (const true of high) & V-const ⟩ ∷ [] ⟩ in
    ∅ ∣ low ⊢ compile M*₂ ⊢M*₂ ⇓ const tt of high ∣ μ
M*₂⇓tt = ⇓-let (⇓-val V-const)
         (⇓-let (⇓-ref (⇓-cast (A-base-proj _) (⇓-val (V-cast V-const (I-base-inj _))) (cast-base-proj h≼h) (⇓-val V-const)) refl)
         (⇓-if-false (⇓-val V-const) (⇓-val V-const)))

M*₁′ M*₂′ : Term
M*₁′ =
  `let ($ true of high) `in
  `let (ref[ high ] ($ true of low {- here -}) ∶ ` Bool of ⋆ at pos 3 at pos 0) `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low at pos 2
M*₂′ =
  `let ($ false of high) `in
  `let (ref[ high ] ($ true of low) ∶ ` Bool of ⋆ at pos 3 at pos 0) `in
    if ` 1 then (` 0) := ($ false of high) at pos 1
           else $ tt of low at pos 2

⊢M*₁′ : [] ; l low ⊢ᴳ M*₁′ ⦂ ` Unit of l high
⊢M*₁′ =
  ⊢let ⊢const
    (⊢let (⊢ref (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)) (≲-ty ≾-⋆l ≲-ι) (≾-l l≼h))
      (⊢if (⊢var refl)
           (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
           ⊢const refl))
⊢M*₂′ : [] ; l low ⊢ᴳ M*₂′ ⦂ ` Unit of l high
⊢M*₂′ =
  ⊢let ⊢const
    (⊢let (⊢ref (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι)) (≲-ty ≾-⋆l ≲-ι) (≾-l l≼h))
      (⊢if (⊢var refl)
           (⊢assign (⊢var refl) ⊢const ≲-refl (≾-l l≼h) ≾-refl)
           ⊢const refl))

M*₁′⇓tt :
  let μ = ⟨ [] , ⟨ 0 , (const false of high) & V-const ⟩ ∷ ⟨ 0 , (const true of low) & V-const ⟩ ∷ [] ⟩ in
    ∅ ∣ low ⊢ compile M*₁′ ⊢M*₁′ ⇓ const tt of high ∣ μ
M*₁′⇓tt = ⇓-let (⇓-val V-const)
         (⇓-let (⇓-ref (⇓-cast (A-base-proj _) (⇓-val (V-cast V-const (I-base-inj _))) (cast-base-proj l≼h) (⇓-val V-const)) refl)
         (⇓-if-true (⇓-val V-const) (⇓-assign (⇓-val V-addr) (⇓-val V-const))))

M*₂′⇓tt :
  let μ = ⟨ [] , ⟨ 0 , (const true of low) & V-const ⟩ ∷ [] ⟩ in
    ∅ ∣ low ⊢ compile M*₂′ ⊢M*₂′ ⇓ const tt of high ∣ μ
M*₂′⇓tt = ⇓-let (⇓-val V-const)
         (⇓-let (⇓-ref (⇓-cast (A-base-proj _) (⇓-val (V-cast V-const (I-base-inj _))) (cast-base-proj l≼h) (⇓-val V-const)) refl)
         (⇓-if-false (⇓-val V-const) (⇓-val V-const)))
