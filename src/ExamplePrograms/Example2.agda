module ExamplePrograms.Example2 where

open import Data.Unit
open import Data.List
open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils
open import Common.Types
open import Common.BlameLabels
open import Surface.SurfaceLang
open import CC.CCStatics renaming (Term to CCTerm;
  `_ to var; $_of_ to const_of_; ƛ⟦_⟧_˙_of_ to lam⟦_⟧_˙_of_; !_ to *_)
open import CC.Compile
open import CC.Reduction
open import CC.MultiStep
open import CC.BigStep
open import Memory.Heap CCTerm Value

open import ExamplePrograms.Common



{- Input is `true` in N₁ and `false` in N₂ -}
N₁ N₂ : Term
N₁ =
  `let ref⟦ low ⟧ ($ true of low) at pos 0 `in
  `let if ($ true of high) ∶ ` Bool of ⋆ at pos 1
         then (` 0) := $ false of low at pos 2
         else (` 0) := $ true  of low at pos 3
         at pos 4 `in
  (publish · (! (` 1)) at pos 5)
N₂ =
  `let ref⟦ low ⟧ ($ true of low) at pos 0 `in
  `let if ($ false of high) ∶ ` Bool of ⋆ at pos 1
         then (` 0) := $ false of low at pos 2
         else (` 0) := $ true  of low at pos 3
         at pos 4 `in
  (publish · (! (` 1)) at pos 5)

⊢N₁ : [] ; l low ⊢ᴳ N₁ ⦂ ` Unit of l low
⊢N₁ =
  ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
       (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  refl)
             (⊢app ⊢publish (⊢deref (⊢var refl)) ≲-refl ≾-refl ≾-refl))
⊢N₂ : [] ; l low ⊢ᴳ N₂ ⦂ ` Unit of l low
⊢N₂ =
  ⊢let (⊢ref ⊢const ≲-refl ≾-refl)
       (⊢let (⊢if (⊢ann ⊢const (≲-ty ≾-⋆r ≲-ι))
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  (⊢assign (⊢var refl) ⊢const ≲-refl ≾-refl ≾-⋆l)
                  refl)
             (⊢app ⊢publish (⊢deref (⊢var refl)) ≲-refl ≾-refl ≾-refl))

𝒞N₁  = compile N₁ ⊢N₁
𝒞N₂  = compile N₂ ⊢N₂
⊢𝒞N₁ = compile-preserve N₁ ⊢N₁
⊢𝒞N₂ = compile-preserve N₂ ⊢N₂

_ :
  𝒞N₁ ≡
  let c₁ = cast (` Bool of l high) (` Bool of ⋆) (pos 1) (~-ty ~⋆ ~-ι) in
  (`let (ref⟦ low ⟧ (const true of low))
  (`let (if (const true of high ⟨ c₁ ⟩) _ (var 0 :=? (const false of low)) (var 0 :=? (const true of low)))
  (compile {[]} publish ⊢publish · (* var 1))))
_ = refl

{- Both N₁ and N₂ evaluate to `nsu-error` -}
_ : ∃[ μ ] ( 𝒞N₁ ∣ ∅ ∣ low —↠ error nsu-error ∣ μ )
_ = ⟨ _ , R* ⟩
  where
  R* =
    𝒞N₁ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} ref-static ⟩
    _ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} (ref V-const refl) ⟩
    _ ∣ ⟨ [ ⟨ 0 , (const true of low) & V-const ⟩ ] , [] ⟩ ∣ low
      —→⟨ β-let V-addr ⟩
    _ ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (if-cast-true (I-base-inj _)) ⟩
    let a = addr a⟦ low ⟧ 0 of low in
    let c = cast (` Unit of l high) (` Unit of ⋆) (pos 1) (~-ty ~⋆ ~-ι) in
    `let (prot high (cast-pc ⋆ (a :=? (const false of low))) ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ {F = cast-pc ⋆ □} (assign?-fail (λ ()) {- high ⋠ low -})))) ⟩
    `let (prot high (cast-pc ⋆ (error nsu-error)) ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ-err {F = cast-pc ⋆ □}))) ⟩
    `let (prot high (error nsu-error) ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} prot-err) ⟩
    `let (error nsu-error ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ-err {F = □⟨ _ ⟩}) ⟩
    `let (error nsu-error) (_ · (* a)) ∣ _ ∣ low
       —→⟨ ξ-err {F = let□ _} ⟩
    error nsu-error ∣ _ ∣ low ∎

_ : ∃[ μ ] ( 𝒞N₂ ∣ ∅ ∣ low —↠ error nsu-error ∣ μ )
_ = ⟨ _ , R* ⟩
  where
  R* =
    𝒞N₂ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} ref-static ⟩
    _ ∣ ∅ ∣ low
      —→⟨ ξ {F = let□ _} (ref V-const refl) ⟩
    _ ∣ ⟨ [ ⟨ 0 , (const true of low) & V-const ⟩ ] , [] ⟩ ∣ low
      —→⟨ β-let V-addr ⟩
    _ ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (if-cast-false (I-base-inj _)) ⟩
    let a = addr a⟦ low ⟧ 0 of low in
    let c = cast (` Unit of l high) (` Unit of ⋆) (pos 1) (~-ty ~⋆ ~-ι) in
    `let (prot high (cast-pc ⋆ (a :=? (const true of low))) ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ {F = cast-pc ⋆ □} (assign?-fail (λ ()) {- high ⋠ low -})))) ⟩
    `let (prot high (cast-pc ⋆ (error nsu-error)) ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
      —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} (prot-ctx (ξ-err {F = cast-pc ⋆ □}))) ⟩
    `let (prot high (error nsu-error) ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ {F = □⟨ _ ⟩} prot-err) ⟩
    `let (error nsu-error ⟨ c ⟩) (_ · (* a)) ∣ _ ∣ low
       —→⟨ ξ {F = let□ _} (ξ-err {F = □⟨ _ ⟩}) ⟩
    `let (error nsu-error) (_ · (* a)) ∣ _ ∣ low
       —→⟨ ξ-err {F = let□ _} ⟩
    error nsu-error ∣ _ ∣ low ∎
