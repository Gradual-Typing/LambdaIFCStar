module Compile.CompilationPresTypes where

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

open import Compile.Compile


{- The compilation from λIFC⋆ to λIFCc preserves types -}
compilation-preserves-type : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
    ----------------------------------------------
  → Γ ; ∅ ; gc ; low ⊢ compile M ⊢M ⇐ A


compile-preserve : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
    -------------------------------------------------
  → (∀ {pc} → Γ ; ∅ ; gc ; pc ⊢ compile M ⊢M ⇐ A)
compile-preserve ($ᴳ k of ℓ) ⊢const = ⊢const
compile-preserve (`ᴳ x) (⊢var Γ∋x) = ⊢var Γ∋x
compile-preserve (ƛ pc , A ˙ N of ℓ) (⊢lam ⊢N) = ⊢lam (compile-preserve N ⊢N)
compile-preserve (L · M at p) (⊢app {gc = gc} {gc′} {A} {A′} {B} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′)
  with all-specific? [ gc , g , gc′ ] | g≾gc′ | gc≾gc′
... | yes (as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) (as-cons (＠ ℓ₃) as-nil))) | ≾-l ℓ≼ℓᶜ | ≾-l pc≼ℓᶜ =
  ⊢app (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)) refl
... | no ¬as | _ | _ with B
...   | T of g = ⊢cast (⊢app⋆ (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M)))
compile-preserve {Γ = Γ} (if L then M else N at p) (⊢if {gc = gc} {A = A} {B} {C} {g = g} ⊢L ⊢M ⊢N A∨̃B≡C) {pc}
  with consis-join-≲-inv {A} {B} A∨̃B≡C
... | ⟨ A≲C , B≲C ⟩
  with all-specific? [ gc , g ] | C
... | yes (as-cons (＠ _) (as-cons (＠ _) as-nil)) | T of g′ =
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
  with all-specific? [ gc , g , ĝ ] | g≾ĝ | gc≾ĝ
... | yes (as-cons (＠ ℓc)  (as-cons (＠ ℓ)  (as-cons (＠ ℓ̂) as-nil))) | ≾-l ℓ≼ℓ̂ | ≾-l ℓc≼ℓ̂ =
  ⊢assign (compile-preserve L ⊢L) (⊢cast (compile-preserve M ⊢M)) ℓc≼ℓ̂ ℓ≼ℓ̂
... | no _ | _ | _ = ⊢assign? (⊢cast (compile-preserve L ⊢L)) (⊢cast (compile-preserve M ⊢M))


compilation-preserves-type M ⊢M = compile-preserve M ⊢M {low}
