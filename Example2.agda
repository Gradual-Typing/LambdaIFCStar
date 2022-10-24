module Example2 where

open import Data.Unit
open import Data.List
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Types
open import BlameLabels
open import SurfaceLang
open import CC renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ[_]_˙_of_ to lam[_]_˙_of_; !_ to *_)
open import Compile
open import Reduction
open import BigStep
open import Heap
open import TypeBasedCast

{- Input is `true` in N₁ and `false` in N₂ -}
N₁ N₂ : Term
N₁ =
  `let ref[ low ] ($ true of low) at pos 0 `in
  `let if ($ true of high) ∶ ` Bool of ⋆ at pos 1
         then (` 0) := $ false of low at pos 2
         else (` 0) := $ true  of low at pos 3
         at pos 4 `in
  ! (` 1)
N₂ =
  `let ref[ low ] ($ true of low) at pos 0 `in
  `let if ($ false of high) ∶ ` Bool of ⋆ at pos 1
         then (` 0) := $ false of low at pos 2
         else (` 0) := $ true  of low at pos 3
         at pos 4 `in
  ! (` 1)

⊢N₁ : [] ; l low ⊢ᴳ N₁ ⦂ ` Bool of l low
⊢N₁ =
  ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
       (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  refl)
             (⊢deref (⊢var refl)))
⊢N₂ : [] ; l low ⊢ᴳ N₂ ⦂ ` Bool of l low
⊢N₂ =
  ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
       (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  refl)
             (⊢deref (⊢var refl)))

N⇒₁ N⇒₂ : CCTerm
N⇒₁ = compile N₁ ⊢N₁; N⇒₂ = compile N₂ ⊢N₂

_ :
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 1) (~-ty ~⋆ ~-ι) in
  N⇒₁ ≡
  (`let (ref[ low ] (const true of low))
  (`let (if (const true of high ⟨ c₁ ⟩) _ (var 0 :=? (const false of low)) (var 0 :=? (const true of low)))
  (* var 1)))
_ = refl

{- Both N₁ and N₂ evaluate to `nsu-error` -}
_ : ∃[ μ ] ( N⇒₁ ∣ ∅ ∣ low —↠ error nsu-error ∣ μ )
_ = ⟨ _ , R* ⟩
  where
  R* =
    N⇒₁ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} ref-static ⟩
    _ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} (ref V-const refl) ⟩
    _ ∣ ⟨ [ ⟨ 0 , (const true of low) & V-const ⟩ ] , [] ⟩ ∣ low
      —→⟨ β-let V-addr ⟩
    _ ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (if-cast-true (I-base-inj _)) ⟩
    let a = addr a[ low ] 0 of low in
    let c = cast (` Unit of l high) (` Unit of ⋆) (pos 1) (~-ty ~⋆ ~-ι) in
    `let (prot high (cast-pc ⋆ (a :=? (const false of low))) ⟨ c ⟩) (* a) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ {F = cast-pc ⋆ □} (assign?-fail (λ ()) {- high ⋠ low -})))) ⟩
    `let (prot high (cast-pc ⋆ (error nsu-error)) ⟨ c ⟩) (* a) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ-err {F = cast-pc ⋆ □}))) ⟩
    `let (prot high (error nsu-error) ⟨ c ⟩) (* a) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} prot-err) ⟩
    `let (error nsu-error ⟨ c ⟩) (* a) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ-err {F = □⟨ _ ⟩}) ⟩
    `let (error nsu-error) (* a) ∣ _ ∣ low
       —→⟨ ξ-err {F = let□ _} ⟩
    error nsu-error ∣ _ ∣ low ∎

_ : ∃[ μ ] ( N⇒₂ ∣ ∅ ∣ low —↠ error nsu-error ∣ μ )
_ = ⟨ _ , R* ⟩
  where
  R* =
    N⇒₂ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} ref-static ⟩
    _ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} (ref V-const refl) ⟩
    _ ∣ ⟨ [ ⟨ 0 , (const true of low) & V-const ⟩ ] , [] ⟩ ∣ low
      —→⟨ β-let V-addr ⟩
    _ ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (if-cast-false (I-base-inj _)) ⟩
    let a = addr a[ low ] 0 of low in
    let c = cast (` Unit of l high) (` Unit of ⋆) (pos 1) (~-ty ~⋆ ~-ι) in
    `let (prot high (cast-pc ⋆ (a :=? (const true of low))) ⟨ c ⟩) (* a) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ {F = cast-pc ⋆ □} (assign?-fail (λ ()) {- high ⋠ low -})))) ⟩
    `let (prot high (cast-pc ⋆ (error nsu-error)) ⟨ c ⟩) (* a) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ-err {F = cast-pc ⋆ □}))) ⟩
    `let (prot high (error nsu-error) ⟨ c ⟩) (* a) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} prot-err) ⟩
    `let (error nsu-error ⟨ c ⟩) (* a) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ-err {F = □⟨ _ ⟩}) ⟩
    `let (error nsu-error) (* a) ∣ _ ∣ low
       —→⟨ ξ-err {F = let□ _} ⟩
    error nsu-error ∣ _ ∣ low ∎


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
