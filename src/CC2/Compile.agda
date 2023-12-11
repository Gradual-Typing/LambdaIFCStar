module CC2.Compile where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Function using (case_of_)

open import Syntax

open import Common.Utils
open import Common.BlameLabels
open import Common.Types
open import Common.TypeBasedCast
open import Surface2.Lang
  renaming (`_ to `ᴳ_;
            $_of_ to $ᴳ_of_)
open import CC2.Syntax public  renaming (Term to CCTerm)
open import CC2.Typing public



compile : ∀ {Γ gc A} (M : Term) → Γ ; gc ⊢ᴳ M ⦂ A → CCTerm
compile ($ᴳ k of ℓ) ⊢const = $ k
compile (`ᴳ x) (⊢var x∈Γ)  = ` x
compile (ƛ g , A ˙ N of ℓ) (⊢lam ⊢N) = ƛ (compile N ⊢N)
compile (L · M at p) (⊢app {gc = gc} {gc′} {A = A} {A′} {B} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′) =
    case ⟨ g≾gc′ , gc≾gc′ , B ⟩ of λ where
    ⟨ ≾-l {ℓ} {ℓᶜ} ℓ≼ℓᶜ , ≾-l {pc} {.ℓᶜ} pc≼ℓᶜ , B ⟩ →
      let sub : ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ <: ⟦ l (pc ⋎ ℓ) ⟧ A ⇒ B of l ℓ
          sub = <:-ty <:ₗ-refl (<:-fun (<:-l (ℓ₁⋎ℓ₂≼ℓ pc≼ℓᶜ ℓ≼ℓᶜ)) <:-refl <:-refl) in
      app (compile L ⊢L ⟨ coerce-<: sub ⟩) (compile M ⊢M ⟨ coerce A′≲A p ⟩) A B ℓ
    ⟨ _ , _ , T of g′ ⟩ →
      let csub₁ : ⟦ gc′ ⟧ A ⇒ (T of g′) of g ≲ ⟦ ⋆ ⟧ A ⇒ (T of ⋆) of ⋆
          csub₁ = ≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl (≲-ty ≾-⋆r ≲ᵣ-refl))
          csub₂ : T of ⋆ ≲ stamp (T of g′) g
          csub₂ = ≲-ty ≾-⋆l ≲ᵣ-refl in
      (app! (compile L ⊢L ⟨ coerce csub₁ p ⟩) (compile M ⊢M ⟨ coerce A′≲A p ⟩) A T) ⟨ coerce csub₂ p ⟩
compile (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C) =
  case consis-join-≲-inv {A} {B} A∨̃B≡C of λ where
  ⟨ A≲C , B≲C ⟩ →
      let L′ = compile L ⊢L in
      let M′ = compile M ⊢M ⟨ coerce A≲C p ⟩ in
      let N′ = compile N ⊢N ⟨ coerce B≲C p ⟩ in
      case ⟨ gc , g , C ⟩ of λ where
      ⟨ l _ , l ℓ , C ⟩ → if L′ C ℓ M′ N′
      ⟨   _ ,   _ , T of g′ ⟩ →
        let csub₁ : ` Bool of g ≲ ` Bool of ⋆
            csub₁ = ≲-ty ≾-⋆r ≲ᵣ-refl in
        let csub₂ : stamp C ⋆ ≲ stamp C g
            csub₂ = proj₁ (~→≲ (stamp-~ ~-refl ⋆~)) in
        let ⟨ A≲C , B≲C ⟩ = consis-join-≲-inv {A} {B} {C} A∨̃B≡C in
        (if! (L′ ⟨ coerce csub₁ p ⟩) T (M′ ⟨ inject T g′ ⟩) (N′ ⟨ inject T g′ ⟩)) ⟨ coerce csub₂ p ⟩
compile (M ∶ A at p) (⊢ann {A′ = A′} ⊢M A′≲A) = compile M ⊢M ⟨ coerce A′≲A p ⟩
compile (`let M `in N) (⊢let {A = A} ⊢M ⊢N) = `let (compile M ⊢M) A (compile N ⊢N)
compile (ref⟦ ℓ ⟧ M at p) (⊢ref {gc = gc} ⊢M Tg≲Tℓ gc≾ℓ) =
  let M′ = compile M ⊢M ⟨ coerce Tg≲Tℓ p ⟩ in
  case gc of λ where
  (l ℓᶜ) →  ref⟦ ℓ ⟧ M′
  ⋆      → ref?⟦ ℓ ⟧ M′ p
compile (! M at p) (⊢deref {A = A} {g} ⊢M) =
  case ⟨ g , A ⟩ of λ where
  ⟨ l ℓ , A       ⟩ → !  (compile M ⊢M) A ℓ
  ⟨ ⋆   , T of g′ ⟩ → !! (compile M ⊢M ⟨ ref-to-⋆ T g′ g p ⟩) T
compile (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) =
  case ⟨ g≾ĝ , gc≾ĝ ⟩ of λ where
  ⟨ ≾-l {ℓ} {ℓ̂} g≼ĝ , ≾-l gc≼ĝ ⟩ →
      assign (compile L ⊢L) (compile M ⊢M ⟨ coerce A≲Tĝ p ⟩) T ℓ̂ ℓ
  ⟨ _ , _ ⟩ →
    let csub : Ref (T of ĝ) of g ≲ Ref (T of ĝ) of ⋆
        csub = ≲-ty ≾-⋆r ≲ᵣ-refl in
      assign? (compile L ⊢L ⟨ coerce csub p ⟩) (compile M ⊢M ⟨ coerce A≲Tĝ p ⟩) T ĝ p


compile-preserve : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
    -------------------------------------------------
  → (∀ {pc} → Γ ; ∅ ; gc ; pc ⊢ compile M ⊢M ⇐ A)
compile-preserve ($ᴳ k of ℓ) ⊢const = ⊢const
compile-preserve (`ᴳ x) (⊢var Γ∋x) = ⊢var Γ∋x
compile-preserve (ƛ pc , A ˙ N of ℓ) (⊢lam ⊢N) = ⊢lam (compile-preserve N ⊢N)
compile-preserve (L · M at p) (⊢app {A = A} {A′} {B} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′)
  with gc≾gc′ | g≾gc′ | B
... | ≾-l gc≼gc′ | ≾-l g≼gc′ | T of g =
  ⊢app (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)) refl
... | ≾-l _ | ≾-⋆l  | T of g = ⊢cast (⊢app! (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆l  | ≾-l _ | T of g = ⊢cast (⊢app! (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆l  | ≾-⋆l  | T of g = ⊢cast (⊢app! (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆l  | ≾-⋆r  | T of g = ⊢cast (⊢app! (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆r  | ≾-⋆l  | T of g = ⊢cast (⊢app! (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆r  | ≾-⋆r  | T of g = ⊢cast (⊢app! (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
compile-preserve {Γ = Γ} (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C) {pc}
  with consis-join-≲-inv {A} {B} A∨̃B≡C
... | ⟨ A≲C , B≲C ⟩
  with gc | g | C
... | l _ | l _ | T of g′ =
  ⊢if (compile-preserve L ⊢L) (⊢cast (compile-preserve M ⊢M)) (⊢cast (compile-preserve N ⊢N)) refl
... | l pc′ | ⋆ | T of g′ =
  ⊢cast ♣
  where
  ♣ : _
  ♣ = subst (λ □ → Γ ; ∅ ; l pc′ ; pc ⊢
               if! (compile L ⊢L ⟨ coerce (≲-ty {g₁ = ⋆} {S = ` Bool} ≾-⋆r ≲ᵣ-refl) p ⟩) T
                   ((compile M ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g′ ⟩)
                   ((compile N ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g′ ⟩) ⇐ □) (cong (_ of_) (sym (g⋎̃⋆≡⋆ {g′})))
            (⊢if! (⊢cast (compile-preserve L ⊢L))
              (⊢cast (⊢cast (compile-preserve M ⊢M))) (⊢cast (⊢cast (compile-preserve N ⊢N))))
... | ⋆ | l ℓ | T of g′ =
  ⊢cast ♣
  where
  ♣ : _
  ♣ = subst (λ □ → Γ ; ∅ ; ⋆ ; pc ⊢
               if! (compile L ⊢L ⟨ coerce (≲-ty {g₁ = l ℓ} {S = ` Bool} ≾-⋆r ≲ᵣ-refl) p ⟩) T
                   ((compile M ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g′ ⟩)
                   ((compile N ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g′ ⟩) ⇐ □) (cong (_ of_) (sym (g⋎̃⋆≡⋆ {g′})))
            (⊢if! (⊢cast (compile-preserve L ⊢L))
              (⊢cast (⊢cast (compile-preserve M ⊢M))) (⊢cast (⊢cast (compile-preserve N ⊢N))))
... | ⋆ | ⋆ | T of g′ =
  ⊢cast ♣
  where
  ♣ : _
  ♣ = subst (λ □ → Γ ; ∅ ; ⋆ ; pc ⊢
               if! (compile L ⊢L ⟨ coerce (≲-ty {g₁ = ⋆} {S = ` Bool} ≾-⋆r ≲ᵣ-refl) p ⟩) T
                   ((compile M ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g′ ⟩)
                   ((compile N ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g′ ⟩) ⇐ □) (cong (_ of_) (sym (g⋎̃⋆≡⋆ {g′})))
            (⊢if! (⊢cast (compile-preserve L ⊢L))
              (⊢cast (⊢cast (compile-preserve M ⊢M))) (⊢cast (⊢cast (compile-preserve N ⊢N))))
compile-preserve (M ∶ A at p) (⊢ann ⊢M A′≲A) = ⊢cast (compile-preserve M ⊢M)
compile-preserve (`let M `in N) (⊢let ⊢M ⊢N) = ⊢let (compile-preserve M ⊢M) (compile-preserve N ⊢N)
compile-preserve (ref⟦ ℓ ⟧ M at p) (⊢ref {gc = gc} {T = T} {g} ⊢M Tg≲Tℓ gc≾ℓ)
  with gc≾ℓ
... | ≾-⋆l = ⊢ref? (⊢cast (compile-preserve M ⊢M))
... | ≾-l ℓᶜ≼ℓ {- gc = ℓᶜ -} = ⊢ref (⊢cast (compile-preserve M ⊢M)) ℓᶜ≼ℓ
compile-preserve (! M at p) (⊢deref {A = A} {g} ⊢M)
  with g | A
... | l _ | T of g′ = ⊢deref  (compile-preserve M ⊢M) refl
... | ⋆   | T of g′ rewrite g⋎̃⋆≡⋆ {g′} = ⊢deref! (⊢cast (compile-preserve M ⊢M))
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ)
  with g≾ĝ | gc≾ĝ
... | ≾-l g≼ĝ | ≾-l gc≼ĝ =
  ⊢assign (compile-preserve L ⊢L) (⊢cast (compile-preserve M ⊢M)) gc≼ĝ g≼ĝ
... | ≾-l _ | ≾-⋆l =
  ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))
... | ≾-⋆r | ≾-⋆r =
  ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))
... | ≾-⋆r | ≾-⋆l =
  ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))
... | ≾-⋆l | ≾-l _ =
  ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))
... | ≾-⋆l | ≾-⋆r =
  ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))
... | ≾-⋆l | ≾-⋆l =
  ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))


{- Compilation from Surface to CC is type-preserving. -}
compilation-preserves-type : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
    ----------------------------------------------
  → Γ ; ∅ ; gc ; low ⊢ compile M ⊢M ⇐ A
compilation-preserves-type M ⊢M = compile-preserve M ⊢M {low}
