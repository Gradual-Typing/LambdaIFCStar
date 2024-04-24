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
      let csub : T of ⋆ ≲ stamp (T of g′) g
          csub = ≲-ty ≾-⋆l ≲ᵣ-refl in
      (app⋆ (compile L ⊢L ⟨ fun-to-⋆ gc′ A T g′ g p ⟩) (compile M ⊢M ⟨ coerce A′≲A p ⟩) A T) ⟨ coerce csub p ⟩
compile (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C) =
  case consis-join-≲-inv {A} {B} A∨̃B≡C of λ where
  ⟨ A≲C , B≲C ⟩ →
      let L′ = compile L ⊢L in
      let M′ = compile M ⊢M ⟨ coerce A≲C p ⟩ in
      let N′ = compile N ⊢N ⟨ coerce B≲C p ⟩ in
      case all-specific-dec [ gc , g ] of λ where
      (yes (as-cons (specific _) (as-cons (specific ℓ) as-nil))) →
        if L′ C ℓ M′ N′
      (no _) →
        case C of λ where
        (T of g′) →
          let csub : stamp C ⋆ ≲ stamp C g
              csub = proj₁ (~→≲ (stamp-~ ~-refl ⋆~)) in
          let ⟨ A≲C , B≲C ⟩ = consis-join-≲-inv {A} {B} {C} A∨̃B≡C in
          (if⋆ (L′ ⟨ inject (` Bool) g ⟩) T (M′ ⟨ inject T g′ ⟩) (N′ ⟨ inject T g′ ⟩)) ⟨ coerce csub p ⟩
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
  ⟨ ⋆   , T of g′ ⟩ → !⋆ (compile M ⊢M ⟨ ref-to-⋆ T g′ g p ⟩) T
compile (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) =
  case all-specific-dec [ gc , g , ĝ ] of λ where
  (yes (as-cons (specific _)  (as-cons (specific ℓ)  (as-cons (specific ℓ̂) as-nil)))) →
      assign (compile L ⊢L) (compile M ⊢M ⟨ coerce A≲Tĝ p ⟩) T ℓ̂ ℓ
  (no _) → assign? (compile L ⊢L ⟨ inject (Ref (T of ĝ)) g ⟩) (compile M ⊢M ⟨ coerce A≲Tĝ p ⟩) T ĝ p


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
... | ≾-l _ | ≾-⋆l  | T of g = ⊢cast (⊢app⋆ (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆l  | ≾-l _ | T of g = ⊢cast (⊢app⋆ (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆l  | ≾-⋆l  | T of g = ⊢cast (⊢app⋆ (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆l  | ≾-⋆r  | T of g = ⊢cast (⊢app⋆ (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆r  | ≾-⋆l  | T of g = ⊢cast (⊢app⋆ (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
... | ≾-⋆r  | ≾-⋆r  | T of g = ⊢cast (⊢app⋆ (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
compile-preserve {Γ = Γ} (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C) {pc}
  with consis-join-≲-inv {A} {B} A∨̃B≡C
... | ⟨ A≲C , B≲C ⟩
  with all-specific-dec [ gc , g ] | C
... | yes (as-cons (specific _) (as-cons (specific _) as-nil)) | T of g′ =
  ⊢if (compile-preserve L ⊢L) (⊢cast (compile-preserve M ⊢M)) (⊢cast (compile-preserve N ⊢N)) refl
... | no ¬as | T of g′ =
  ⊢cast (subst (λ □ → _ ; _ ; _ ; _ ⊢ if⋆ (compile L ⊢L ⟨ inject (` Bool) g ⟩) T
      ((compile M ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g′ ⟩)
      ((compile N ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g′ ⟩) ⇐ T of □) (sym (g⋎̃⋆≡⋆ {g′})) ♣)
  where
  ◆ₘ : ∀ {ℓ} → Γ ; ∅ ; gc ⋎̃ g ; ℓ ⊢ (compile M ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g′ ⟩ ⇐ T of ⋆
  ◆ₘ = ⊢cast (⊢cast (compile-preserve M ⊢M))
  ♥ₘ : ∀ {ℓ} → Γ ; ∅ ; ⋆ ; ℓ ⊢ _ ⇐ T of ⋆
  ♥ₘ = subst (λ □ → ∀ {ℓ} → _ ; _ ; □ ; ℓ ⊢ (compile M ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g′ ⟩ ⇐ _)
             (consis-join-not-all-specific ¬as) ◆ₘ
  ◆ₙ : ∀ {ℓ} → Γ ; ∅ ; gc ⋎̃ g ; ℓ ⊢ (compile N ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g′ ⟩ ⇐ T of ⋆
  ◆ₙ = ⊢cast (⊢cast (compile-preserve N ⊢N))
  ♥ₙ : ∀ {ℓ} → Γ ; ∅ ; ⋆ ; ℓ ⊢ _ ⇐ T of ⋆
  ♥ₙ = subst (λ □ → ∀ {ℓ} → _ ; _ ; □ ; ℓ ⊢ (compile N ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g′ ⟩ ⇐ _)
             (consis-join-not-all-specific ¬as) ◆ₙ
  ♣ : Γ ; ∅ ; gc ; pc ⊢
        if⋆ (compile L ⊢L ⟨ inject (` Bool) g ⟩) T
            ((compile M ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g′ ⟩)
            ((compile N ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g′ ⟩)
        ⇐ T of ⋆
  ♣ = ⊢if⋆ (⊢cast (compile-preserve L ⊢L)) ♥ₘ ♥ₙ
compile-preserve (M ∶ A at p) (⊢ann ⊢M A′≲A) = ⊢cast (compile-preserve M ⊢M)
compile-preserve (`let M `in N) (⊢let ⊢M ⊢N) = ⊢let (compile-preserve M ⊢M) (compile-preserve N ⊢N)
compile-preserve (ref⟦ ℓ ⟧ M at p) (⊢ref {gc = gc} {T = T} {g} ⊢M Tg≲Tℓ gc≾ℓ)
  with gc≾ℓ
... | ≾-⋆l = ⊢ref? (⊢cast (compile-preserve M ⊢M))
... | ≾-l ℓᶜ≼ℓ {- gc = ℓᶜ -} = ⊢ref (⊢cast (compile-preserve M ⊢M)) ℓᶜ≼ℓ
compile-preserve (! M at p) (⊢deref {A = A} {g} ⊢M)
  with g | A
... | l _ | T of g′ = ⊢deref  (compile-preserve M ⊢M) refl
... | ⋆   | T of g′ rewrite g⋎̃⋆≡⋆ {g′} = ⊢deref⋆ (⊢cast (compile-preserve M ⊢M))
compile-preserve (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ)
  with all-specific-dec [ gc , g , ĝ ] | g≾ĝ | gc≾ĝ
... | yes (as-cons (specific ℓc)  (as-cons (specific ℓ)  (as-cons (specific ℓ̂) as-nil))) | ≾-l ℓ≼ℓ̂ | ≾-l ℓc≼ℓ̂ =
  ⊢assign (compile-preserve L ⊢L) (⊢cast (compile-preserve M ⊢M)) ℓc≼ℓ̂ ℓ≼ℓ̂
... | no _ | _ | _ = ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))


{- Compilation from Surface to CC is type-preserving. -}
compilation-preserves-type : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
    ----------------------------------------------
  → Γ ; ∅ ; gc ; low ⊢ compile M ⊢M ⇐ A
compilation-preserves-type M ⊢M = compile-preserve M ⊢M {low}
