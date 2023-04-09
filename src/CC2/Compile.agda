module CC2.Compile where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)

open import Syntax

open import Common.Utils
open import Common.BlameLabels
open import Common.Types
open import Common.TypeBasedCast
open import Surface2.Lang
  renaming (`_ to `ᴳ_;
            $_of_ to $ᴳ_of_;
            !_ to !ᴳ_)
open import CC2.Syntax Cast_⇒_ public  renaming (Term to CCTerm)
open import CC2.Typing Cast_⇒_ public



compile : ∀ {Γ gc A} (M : Term) → Γ ; gc ⊢ᴳ M ⦂ A → CCTerm
compile ($ᴳ k of ℓ) ⊢const = $ k of ℓ
compile (`ᴳ x) (⊢var x∈Γ)  = ` x
compile (ƛ g , A ˙ N of ℓ) (⊢lam {A = .A} {B} ⊢N) =
  let N′ = compile N ⊢N in
  ƛ g ˙ N′ ∶ A ⇒ B of ℓ
compile (L · M at p) (⊢app {gc = gc} {gc′} {A = A} {A′} {B} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′) =
  case ≲-prop A′≲A of λ where
  ⟨ C , A′~C , C<:A ⟩ →
    case ⟨ g≾gc′ , gc≾gc′ ⟩ of λ where
    ⟨ ≾-l {ℓ} {ℓᶜ} _ , ≾-l _ ⟩ →
      app (compile L ⊢L) (compile M ⊢M ⟨ cast A′ C p A′~C ⟩) ℓᶜ A B ℓ
    ⟨ _ , _ ⟩ →
      let c~₁ : ⟦ gc′ ⟧ A ⇒ B of g ~ ⟦ ⋆ ⟧ A ⇒ B of ⋆
          c~₁ = ~-ty ~⋆ (~-fun ~⋆ ~-refl ~-refl) in
      let c~₂ : stamp B ⋆ ~ stamp B g
          c~₂ = stamp-~ ~-refl ⋆~ in
      (app? (compile L ⊢L ⟨ cast _ _ p c~₁ ⟩) (compile M ⊢M ⟨ cast A′ C p A′~C ⟩) A B p) ⟨ cast _ _ p c~₂ ⟩
compile (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C) =
  case consis-join-≲-inv {A} {B} A∨̃B≡C of λ where
  ⟨ A≲C , B≲C ⟩ →
    case ⟨ ≲-prop A≲C , ≲-prop B≲C ⟩ of λ where
    ⟨ ⟨ A′ , A~A′ , A′<:C ⟩ , ⟨ B′ , B~B′ , B′<:C ⟩ ⟩ →
      let L′ = compile L ⊢L in
      let M′ = compile M ⊢M ⟨ cast A A′ p A~A′ ⟩ in
      let N′ = compile N ⊢N ⟨ cast B B′ p B~B′ ⟩ in
      case ⟨ gc , g ⟩ of λ where
      ⟨ l _ , l ℓ ⟩ → if L′ C ℓ M′ N′
      ⟨   _ ,   _ ⟩ →
        let c~₁ : ` Bool of g ~ ` Bool of ⋆
            c~₁ = ~-ty ~⋆ ~-ι in
        let c~₂ : stamp C ⋆ ~ stamp C g
            c~₂ = stamp-~ ~-refl ⋆~ in
        (if⋆ (L′ ⟨ cast _ _ p c~₁ ⟩) C M′ N′) ⟨ cast _ _ p c~₂ ⟩
compile (M ∶ A at p) (⊢ann {A′ = A′} ⊢M A′≲A) =
  case ≲-prop A′≲A of λ where
  ⟨ B , A′~B , B<:A ⟩ → compile M ⊢M ⟨ cast A′ B p A′~B ⟩
compile (`let M `in N) (⊢let {A = A} ⊢M ⊢N) =
  let M′ = compile M ⊢M in
  let N′ = compile N ⊢N in
  `let M′ A N′
compile (ref⟦ ℓ ⟧ M at p) (⊢ref {gc = gc} {T = T} {g} ⊢M Tg≲Tℓ gc≾ℓ) =
  case ≲-prop Tg≲Tℓ of λ where
  ⟨ A , Tg~A , A<:Tℓ ⟩ →
    let M′ = compile M ⊢M ⟨ cast (T of g) A p Tg~A ⟩ in
      case gc≾ℓ of λ where
      ≾-⋆l       → ref?⟦ ℓ ⟧ T M′ p
      (≾-l ℓᶜ≼ℓ) →  ref⟦ ℓ ⟧ T M′
compile (!ᴳ M) (⊢deref {A = A} {g} ⊢M) =
  let M′ = compile M ⊢M in ! M′ A g
compile (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) =
  case ⟨ g≾ĝ , gc≾ĝ ⟩ of λ where
  ⟨ ≾-l {ℓ} {ℓ̂} g≼ĝ , ≾-l gc≼ĝ ⟩ →
    case ≲-prop A≲Tĝ of λ where
    ⟨ B , A~B , B<:Tĝ ⟩ →
      assign (compile L ⊢L) (compile M ⊢M ⟨ cast A B p A~B ⟩) T ℓ̂ ℓ
  ⟨ _ , _ ⟩ →
    let A≲T⋆ = A≲Tg→A≲T⋆ A≲Tĝ in
    case ≲-prop A≲T⋆ of λ where
    ⟨ B , A~B , B<:T⋆ ⟩ →
      let c~ : Ref (T of ĝ) of g ~ Ref (T of ⋆) of ⋆
          c~ = ~-ty ~⋆ (~-ref (~-ty ~⋆ ~ᵣ-refl)) in
      assign? (compile L ⊢L ⟨ cast _ _ p c~ ⟩) (compile M ⊢M ⟨ cast A B p A~B ⟩) T p


compile-preserve : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
    -------------------------------------------------
  → (∀ {pc} → Γ ; ∅ ; gc ; pc ⊢ compile M ⊢M ⇐ A)
compile-preserve ($ᴳ k of ℓ) ⊢const = ⊢const <:-refl
compile-preserve (`ᴳ x) (⊢var Γ∋x) = ⊢var Γ∋x <:-refl
compile-preserve (ƛ pc , A ˙ N of ℓ) (⊢lam ⊢N) = ⊢lam (compile-preserve N ⊢N) <:-refl
compile-preserve (L · M at p) (⊢app {gc = gc} {gc′} {A = A} {A′} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′)
  with ≲-prop A′≲A
... | ⟨ B , A′~B , B<:A ⟩
  with gc≾gc′ | g≾gc′
...   | ≾-l gc≼gc′ | ≾-l g≼gc′ =
  ⊢app (compile-preserve L ⊢L) (⊢cast (compile-preserve M ⊢M) B<:A) gc≼gc′ g≼gc′
...   | ≾-l _ | ≾-⋆l  = ⊢cast (⊢app? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:A)) <:-refl
...   | ≾-⋆l  | ≾-l _ = ⊢cast (⊢app? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:A)) <:-refl
...   | ≾-⋆l  | ≾-⋆l  = ⊢cast (⊢app? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:A)) <:-refl
...   | ≾-⋆l  | ≾-⋆r  = ⊢cast (⊢app? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:A)) <:-refl
...   | ≾-⋆r  | ≾-⋆l  = ⊢cast (⊢app? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:A)) <:-refl
...   | ≾-⋆r  | ≾-⋆r  = ⊢cast (⊢app? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:A)) <:-refl
compile-preserve (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C)
  with consis-join-≲-inv {A} {B} A∨̃B≡C
... | ⟨ A≲C , B≲C ⟩
  with ≲-prop A≲C | ≲-prop B≲C
... | ⟨ A′ , A~A′ , A′<:C ⟩ | ⟨ B′ , B~B′ , B′<:C ⟩
  with gc | g
... | l _ | l _ =
  ⊢if (compile-preserve L ⊢L)
      (⊢cast {c = cast _ _ _ A~A′} (compile-preserve M ⊢M) A′<:C)
      (⊢cast (compile-preserve N ⊢N) B′<:C)
... | l pc′ | ⋆ =
  ⊢cast (⊢if⋆ (⊢cast (compile-preserve L ⊢L) <:-refl)
    (⊢cast (compile-preserve M ⊢M) A′<:C) (⊢cast (compile-preserve N ⊢N) B′<:C)) <:-refl
... | ⋆ | l ℓ =
  ⊢cast (⊢if⋆ (⊢cast (compile-preserve L ⊢L) <:-refl)
    (⊢cast (compile-preserve M ⊢M) A′<:C) (⊢cast (compile-preserve N ⊢N) B′<:C)) <:-refl
... | ⋆ | ⋆ =
  ⊢cast (⊢if⋆ (⊢cast (compile-preserve L ⊢L) <:-refl)
    (⊢cast (compile-preserve M ⊢M) A′<:C) (⊢cast (compile-preserve N ⊢N) B′<:C)) <:-refl
compile-preserve {Γ} {Σ} {A = A} (M ∶ A at p) (⊢ann {A′ = A′} ⊢M A′≲A)
  with ≲-prop A′≲A
... | ⟨ B , A′~B , B<:A ⟩ = ⊢cast (compile-preserve M ⊢M) B<:A
compile-preserve (`let M `in N) (⊢let ⊢M ⊢N) =
  ⊢let (compile-preserve M ⊢M) (compile-preserve N ⊢N)
compile-preserve (ref⟦ ℓ ⟧ M at p) (⊢ref {gc = gc} {T = T} {g} ⊢M Tg≲Tℓ gc≾ℓ)
  with ≲-prop Tg≲Tℓ
... | ⟨ A , Tg~A , A<:Tℓ ⟩
  with gc≾ℓ
...   | ≾-⋆l = ⊢ref? (⊢cast (compile-preserve M ⊢M) A<:Tℓ)
...   | ≾-l ℓᶜ≼ℓ {- gc = ℓᶜ -} = ⊢ref (⊢cast (compile-preserve M ⊢M) A<:Tℓ) ℓᶜ≼ℓ
compile-preserve (!ᴳ M) (⊢deref ⊢M) = ⊢deref (compile-preserve M ⊢M)
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ)
  with g≾ĝ | gc≾ĝ
... | ≾-l g≼ĝ | ≾-l gc≼ĝ
  with ≲-prop A≲Tĝ
...   | ⟨ B , A~B , B<:Tĝ ⟩ =
  ⊢assign (compile-preserve L ⊢L) (⊢cast (compile-preserve M ⊢M) B<:Tĝ) g≼ĝ gc≼ĝ
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) | ≾-l _ | ≾-⋆l
  with ≲-prop (A≲Tg→A≲T⋆ A≲Tĝ)
...   | ⟨ B , A~B , B<:T⋆ ⟩ =
  ⊢assign? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:T⋆)
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) | ≾-⋆r | ≾-⋆r
  with ≲-prop (A≲Tg→A≲T⋆ A≲Tĝ)
...   | ⟨ B , A~B , B<:T⋆ ⟩ =
  ⊢assign? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:T⋆)
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) | ≾-⋆r | ≾-⋆l
  with ≲-prop (A≲Tg→A≲T⋆ A≲Tĝ)
...   | ⟨ B , A~B , B<:T⋆ ⟩ =
  ⊢assign? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:T⋆)
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) | ≾-⋆l | ≾-l _
  with ≲-prop (A≲Tg→A≲T⋆ A≲Tĝ)
...   | ⟨ B , A~B , B<:T⋆ ⟩ =
  ⊢assign? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:T⋆)
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) | ≾-⋆l | ≾-⋆r
  with ≲-prop (A≲Tg→A≲T⋆ A≲Tĝ)
...   | ⟨ B , A~B , B<:T⋆ ⟩ =
  ⊢assign? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:T⋆)
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) | ≾-⋆l | ≾-⋆l
  with ≲-prop (A≲Tg→A≲T⋆ A≲Tĝ)
...   | ⟨ B , A~B , B<:T⋆ ⟩ =
  ⊢assign? (⊢cast (compile-preserve L ⊢L) <:-refl) (⊢cast (compile-preserve M ⊢M) B<:T⋆)


{- Compilation from Surface to CC is type-preserving. -}
compilation-preserves-type : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
    ----------------------------------------------
  → Γ ; ∅ ; gc ; low ⊢ compile M ⊢M ⇐ A
compilation-preserves-type M ⊢M = compile-preserve M ⊢M {low}
