module Example1 where

open import Data.Unit
open import Data.List
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Types
open import BlameLabels
open import SurfaceLang
open import CC renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ⟦_⟧_˙_of_ to lam⟦_⟧_˙_of_; !_ to deref)
open import Compile
open import Reduction
open import BigStep
open import Heap
open import TypeBasedCast


open import ExampleCommon

A₁ : Type
A₁ =  ⟦ ⋆ ⟧ (` Bool of ⋆) ⇒ (` Bool of l high) of l low

A₂ : Type
A₂ = Ref (` Unit of ⋆) of l high

_ : Term
_ = (ƛ⟦ low ⟧ ` Bool of ⋆ ˙ ` 0 of high) · (` 0) at pos 0

{- Explicit type annotation: -}
_ : Term
_ =
  `let ($ true of high) ∶ ` Bool of ⋆ at pos 0 `in
  (` 0)


{- Statically accepted: -}
N : Term
N =
  -- dumb    : 𝔹 of high → 𝔹 of low
  `let ƛ⟦ low ⟧ ` Bool of l high ˙ $ false of low of low `in
  -- input   : 𝔹 of high
  `let (user-input · $ tt of low at pos 0) `in
  -- result  : 𝔹 of low
  `let ` 1 {- dumb -} · ` 0 {- input -} at pos 1 `in
    (publish {- publish -} · ` 0 {- result -} at pos 2)

{- `N` is well-typed -}
⊢N : [] ; l low ⊢ᴳ N ⦂ ` Unit of l low
⊢N =
  (⊢let (⊢lam ⊢const)
  (⊢let (⊢app ⊢user-input ⊢const ≲-refl ≾-refl ≾-refl)
  (⊢let (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl)
    (⊢app ⊢publish (⊢var refl) ≲-refl ≾-refl ≾-refl))))

{- `N` evaluates to `tt` -}
_ : ∅ ∣ low ⊢ compile N ⊢N ⇓ const tt of low ∣ ∅
_ = ⇓-let (⇓-val V-ƛ)
           (⇓-let (⇓-app (⇓-val V-ƛ) (⇓-val V-const) (⇓-val V-const))
                   (⇓-let (⇓-app (⇓-val V-ƛ) (⇓-val V-const) (⇓-val V-const))
                           (⇓-app (⇓-val V-ƛ) (⇓-val V-const) (⇓-val V-const))))

{- Statically rejected because of explicit flow -}
N′ : Term
N′ =
  -- id      : 𝔹 of low → 𝔹 of low
  `let ƛ⟦ low ⟧ ` Bool of l low ˙ ` 0 of low `in
  -- input   : 𝔹 of high
  `let (user-input · $ tt of low at pos 0) `in
  -- result  : 𝔹 of low
  `let ` 1 {- dumb -} · ` 0 {- input -} at pos 1 `in
    (publish {- publish -} · ` 0 {- result -} at pos 2)

-- ⊢N′ : [] ; l low ⊢ᴳ N′ ⦂ ` Unit of l low
-- ⊢N′ =
--   (⊢let (⊢lam (⊢var refl))
--   (⊢let (⊢app ⊢user-input ⊢const ≲-refl ≾-refl ≾-refl)
--   (⊢let (⊢app (⊢var refl) (⊢var refl) (≲-ty (≾-l {!!} {- high ⋠ low -}) ≲-ι) ≾-refl ≾-refl)
--     (⊢app ⊢publish (⊢var refl) ≲-refl ≾-refl ≾-refl))))


{- Statically rejected because of implicit flow -}
M : Term
M =
  -- flip    : 𝔹 of high → 𝔹 of low
  `let (ƛ⟦ low ⟧ ` Bool of l high ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low) ∶
       ⟦ l low ⟧ (` Bool of l high) ⇒ (` Bool of l low) of l low at pos 1 `in
  -- input   : 𝔹 of high
  `let (user-input · $ tt of low at pos 1) `in
  -- result  : 𝔹 of low
  `let ` 1 {- flip -} · ` 0 {- input -} at pos 2 `in
    (publish · ` 0 {- result -} at pos 3)

-- ⊢M : [] ; l low ⊢ᴳ M ⦂ ` Unit of l low
-- ⊢M =
--   (⊢let (⊢ann (⊢lam (⊢if (⊢var refl) ⊢const ⊢const refl)) {!!} {- 𝔹 of high → 𝔹 of high ⋦ 𝔹 of high → 𝔹 of low-})
--   (⊢let (⊢app ⊢user-input ⊢const ≲-refl ≾-refl ≾-refl)
--   (⊢let (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl)
--     (⊢app ⊢publish (⊢var refl) ≲-refl ≾-refl ≾-refl))))


{- We can make the type annotation of `flip` to be more dynamic and defer the checking until runtime: -}
M* : Term
M* =
  -- flip    : 𝔹 of ⋆ → 𝔹 of low
  `let (ƛ⟦ low ⟧ ` Bool of ⋆ ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low) ∶
       ⟦ l low ⟧ (` Bool of ⋆) ⇒ (` Bool of l low) of l low at pos 1 `in
  -- input   : 𝔹 of high
  `let (user-input · $ tt of low at pos 2) `in
  -- result  : 𝔹 of low
  `let ` 1 {- flip -} · ` 0 {- input -} at pos 3 `in
    (publish · ` 0 {- result -} at pos 4)

⊢M* : [] ; l low ⊢ᴳ M* ⦂ ` Unit of l low
⊢M* =
  (⊢let (⊢ann (⊢lam (⊢if (⊢var refl) ⊢const ⊢const refl)) (≲-ty ≾-refl (≲-fun ≾-refl (≲-ty ≾-⋆r ≲ᵣ-refl) (≲-ty ≾-⋆l ≲ᵣ-refl))))
  (⊢let (⊢app ⊢user-input ⊢const ≲-refl ≾-refl ≾-refl)
  (⊢let (⊢app (⊢var refl) (⊢var refl) (≲-ty ≾-⋆r ≲-ι) ≾-refl ≾-refl)
    (⊢app ⊢publish (⊢var refl) (≲-ty ≾-refl ≲ᵣ-refl) ≾-refl ≾-refl))))


{- Alternatively, we can give `result` an extra annotation: -}
M*′ : Term
M*′ =
  -- flip    : 𝔹 of high → 𝔹 of high
  `let ƛ⟦ low ⟧ ` Bool of l high ˙ if (` 0) then $ false of low else $ true of low at (pos 0) of low `in
  -- input   : 𝔹 of high
  `let (user-input · $ tt of low at pos 1) `in
  -- result  : 𝔹 of ⋆
  `let (` 1 {- flip -} · ` 0 {- input -} at pos 2) ∶ ` Bool of ⋆ at pos 3 `in
    (publish · ` 0 {- result -} at pos 4)

{- It's well-typed too -}
⊢M*′ : [] ; l low ⊢ᴳ M*′ ⦂ ` Unit of l low
⊢M*′ =
  (⊢let (⊢lam (⊢if (⊢var refl) ⊢const ⊢const refl))
  (⊢let (⊢app ⊢user-input ⊢const ≲-refl ≾-refl ≾-refl)
  (⊢let (⊢ann (⊢app (⊢var refl) (⊢var refl) ≲-refl ≾-refl ≾-refl) (≲-ty ≾-⋆r ≲ᵣ-refl))
    (⊢app ⊢publish (⊢var refl) (≲-ty ≾-⋆l ≲ᵣ-refl) ≾-refl ≾-refl))))


{- Let's compile M* into CC -}
M*⇒ : CCTerm
M*⇒ = compile M* ⊢M*

{- Take a look at the compiled CC term. Note the casts inserted: -}
eq :
  let c~  = ~-ty ~ₗ-refl (~-fun ~ₗ-refl (~-ty ⋆~ ~-ι) (~-ty ⋆~ ~-ι)) in
  let c₁  = cast (⟦ l low ⟧ (` Bool of ⋆) ⇒ (` Bool of ⋆) of l low)
                 (⟦ l low ⟧ (` Bool of ⋆) ⇒ (` Bool of l low) of l low)
                 (pos 1) c~ in
  let c₂  = cast (` Bool of l high) (` Bool of ⋆) (pos 3) (~-ty ~⋆ ~-ι) in
  M*⇒ ≡
  (`let (lam⟦ low ⟧ ` Bool of ⋆ ˙ if (var 0) (` Bool of l low) (const false of low) (const true of low) of low ⟨ c₁ ⟩)
  (`let (compile {[]} user-input ⊢user-input · const tt of low)
  (`let (var 1 · var 0 ⟨ c₂ ⟩)
  (compile {[]} publish ⊢publish · var 0))))
eq = refl

Rd : M*⇒ ∣ ∅ ∣ low —↠ error (blame (pos 1)) ∣ ∅
Rd =
  M*⇒ ∣ ∅ ∣ low
    —→⟨ β-let (V-cast V-ƛ (I-fun _ I-label I-label)) ⟩
  _    ∣ ∅ ∣ low
    —→⟨ ξ {F = let□ _} (β V-const) ⟩
  _    ∣ ∅ ∣ low
    —→⟨ ξ {F = let□ _} (prot-val V-const) ⟩
  _    ∣ ∅ ∣ low
    —→⟨ β-let V-const ⟩
  let c₁ = cast (⟦ _ ⟧ (` Bool of ⋆) ⇒ (` Bool of ⋆) of _) (⟦ _ ⟧ (` Bool of ⋆) ⇒ (` Bool of l low) of _ ) (pos 1) _ in
  let c₂ = cast (` Bool of l high) (` Bool of ⋆) (pos 3) _ in
  `let (lam⟦ low ⟧ _ ˙ if (var 0) _ _ _ of low ⟨ c₁ ⟩ · const true of high ⟨ c₂ ⟩) _ ∣ ∅ ∣ low  {- 1 -}
    —→⟨ ξ {F = let□ _} (fun-cast V-ƛ (V-cast V-const (I-base-inj _)) (I-fun _ I-label I-label)) ⟩  {- ξ fun-cast -}
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 3) _ in
  let c₂ = cast (` Bool of ⋆) (` Bool of ⋆) (pos 1) _      in
  let c₃ = cast (` Bool of ⋆) (` Bool of l low) (pos 1) _  in
  `let ((lam⟦ low ⟧ _ ˙ if (var 0) _ _ _ of low · const true of high ⟨ c₁ ⟩ ⟨ c₂ ⟩) ⟨ c₃ ⟩) _ ∣ ∅ ∣ low  {- 2 -}
    —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (ξ {F = (_ ·□) V-ƛ} (cast (V-cast V-const (I-base-inj _)) (A-base-id _) cast-base-id))) ⟩
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 3) _ in
  let c₂ = cast (` Bool of ⋆) (` Bool of l low) (pos 1) _  in
  `let ((lam⟦ low ⟧ _ ˙ _ of low · const true of high ⟨ c₁ ⟩) ⟨ c₂ ⟩) _ ∣ ∅ ∣ low  {- 3 -}
    —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (β (V-cast V-const (I-base-inj _)))) ⟩  {- ξ ξ β -}
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 3) _ in
  let c₂ = cast (` Bool of ⋆) (` Bool of l low) (pos 1) _ in
  `let (prot low (if (const true of high ⟨ c₁ ⟩) _ (const false of low) _) ⟨ c₂ ⟩) _ ∣ ∅ ∣ low  {- 4 -}
    —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (if-cast-true (I-base-inj _)))) ⟩  {- ξ ξ prot-ctx if-cast-true -}
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 3) _ in
  let c₂ = cast (` Bool of ⋆) (` Bool of l low) (pos 1) _ in
  `let (prot low (prot high (cast-pc ⋆ (const false of low)) ⟨ c₁ ⟩) ⟨ c₂ ⟩) _ ∣ ∅ ∣ low  {- 5 -}
    —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ {F = □⟨ _ ⟩} (prot-ctx (β-cast-pc V-const))))) ⟩
  _ ∣ ∅ ∣ low
    —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ {F = □⟨ _ ⟩} (prot-val V-const)))) ⟩
  _ ∣ ∅ ∣ low
    —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-val (V-cast V-const (I-base-inj _)))) ⟩
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 3) _ in
  let c₂ = cast (` Bool of ⋆) (` Bool of l low) (pos 1) _ in
  `let (const false of high ⟨ c₁ ⟩ ⟨ c₂ ⟩) _ ∣ ∅ ∣ low  {- 6 -}
    —→⟨ ξ {F = let□ _} (cast (V-cast V-const (I-base-inj _)) (A-base-proj _) (cast-base-proj-blame (λ ()) {- high ⋠ low -})) ⟩
  `let (error (blame (pos 1))) _ ∣ ∅ ∣ low  {- 7 -}
    —→⟨ ξ-err {F = let□ _} ⟩
  error (blame (pos 1)) ∣ ∅ ∣ _  {- 8 -}
    ∎
