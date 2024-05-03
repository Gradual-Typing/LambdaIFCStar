module Compile.Compile where

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
open import Surface2.Lang     renaming (`_ to `ᴳ_;
                                        $_of_ to $ᴳ_of_)
open import CC2.Syntax public renaming (Term to CCTerm)
open import CC2.Typing public


compile : ∀ {Γ gc A} (M : Term) → Γ ; gc ⊢ᴳ M ⦂ A → CCTerm
compile ($ᴳ k of ℓ) ⊢const = $ k
compile (`ᴳ x) (⊢var x∈Γ)  = ` x
compile (ƛ g , A ˙ N of ℓ) (⊢lam ⊢N) = ƛ (compile N ⊢N)
compile (L · M at p) (⊢app {gc = gc} {gc′} {A = A} {A′} {B} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′) =
  case all-specific? [ gc , g , gc′ ] of λ where
  (yes (as-cons (＠ ℓ₁)  (as-cons (＠ ℓ₂)  (as-cons (＠ ℓ₃) as-nil)))) →
    case ⟨ g≾gc′ , gc≾gc′ ⟩ of λ where
    ⟨ ≾-l ℓ≼ℓᶜ , ≾-l pc≼ℓᶜ ⟩ →
      let sub : ⟦ l ℓ₃ ⟧ A ⇒ B of l ℓ₂ <: ⟦ l (ℓ₁ ⋎ ℓ₂) ⟧ A ⇒ B of l ℓ₂
          sub = <:-ty <:ₗ-refl (<:-fun (<:-l (ℓ₁⋎ℓ₂≼ℓ pc≼ℓᶜ ℓ≼ℓᶜ)) <:-refl <:-refl) in
      app (compile L ⊢L ⟨ coerce (<:→≲ sub) p ⟩) (compile M ⊢M ⟨ coerce A′≲A p ⟩) A B ℓ₂
  (no _) →
    case B of λ where
    (T of g′) →
      let csub₁ : ⟦ gc′ ⟧ A ⇒ (T of g′) of g ≲ ⟦ ⋆ ⟧ A ⇒ (T of ⋆) of ⋆
          csub₁ = ≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl (≲-ty ≾-⋆r ≲ᵣ-refl)) in
      let csub₂ : T of ⋆ ≲ stamp (T of g′) g
          csub₂ = ≲-ty ≾-⋆l ≲ᵣ-refl in
      (app⋆ (compile L ⊢L ⟨ coerce csub₁ p ⟩) (compile M ⊢M ⟨ coerce A′≲A p ⟩) A T) ⟨ coerce csub₂ p ⟩
compile (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C) =
  case consis-join-≲-inv {A} {B} A∨̃B≡C of λ where
  ⟨ A≲C , B≲C ⟩ →
      let L′ = compile L ⊢L in
      let M′ = compile M ⊢M ⟨ coerce A≲C p ⟩ in
      let N′ = compile N ⊢N ⟨ coerce B≲C p ⟩ in
      case all-specific? [ gc , g ] of λ where
      (yes (as-cons (＠ _) (as-cons (＠ ℓ) as-nil))) →
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
  case g of λ where
  (l ℓ) → !  (compile M ⊢M) A ℓ
  ⋆     →
    case A of λ where
    (T of g′) →
      let csub : Ref (T of g′) of g ≲ Ref (T of ⋆) of ⋆
          csub = ≲-ty ≾-⋆r (≲-ref (≲-ty ≾-⋆r ≲ᵣ-refl) (≲-ty ≾-⋆l ≲ᵣ-refl)) in
      !⋆ (compile M ⊢M ⟨ coerce csub p ⟩) T
compile (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {ĝ} ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ) =
  case all-specific? [ gc , g , ĝ ] of λ where
  (yes (as-cons (＠ _)  (as-cons (＠ ℓ)  (as-cons (＠ ℓ̂) as-nil)))) →
      assign (compile L ⊢L) (compile M ⊢M ⟨ coerce A≲Tĝ p ⟩) T ℓ̂ ℓ
  (no _) →
    assign? (compile L ⊢L ⟨ inject (Ref (T of ĝ)) g ⟩) (compile M ⊢M ⟨ coerce A≲Tĝ p ⟩) T ĝ p
