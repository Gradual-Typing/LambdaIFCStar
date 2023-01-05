module CCExpSub.Uniqueness where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Syntax

open import Common.Utils
open import Common.Types
open import Common.SubtypeCast
open import Common.TypeBasedCast
open import Memory.HeapContext
open import CCExpSub.Syntax Cast_⇒_
open import CCExpSub.Typing Cast_⇒_


{- The `cast` term is honest about the casted term's type -}
cast-wt-inv : ∀ {Γ Σ gc pc A B M} {c : Cast A ⇒ B}
  → Γ ; Σ ; gc ; pc ⊢ M ⟨ c ⟩ ⦂ B
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
cast-wt-inv (⊢cast ⊢M)              = ⊢M
cast-wt-inv (⊢sub-pc ⊢M⟨c⟩ gc<:gc′) = ⊢sub-pc (cast-wt-inv ⊢M⟨c⟩) gc<:gc′

sub-wt-inv : ∀ {Γ Σ gc pc A B M} {s : A ↟ B}
  → Γ ; Σ ; gc ; pc ⊢ M ↟⟨ s ⟩ ⦂ B
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
sub-wt-inv (⊢sub ⊢M)              = ⊢M
sub-wt-inv (⊢sub-pc ⊢M↟ gc<:gc′) = ⊢sub-pc (sub-wt-inv ⊢M↟) gc<:gc′

private
  lookup-unique : ∀ {Γ} {A B : Type} (x : Var) → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
  lookup-unique {_ ∷ Γ} 0 refl refl = refl
  lookup-unique {_ ∷ Γ} (suc x) Γ∋x⦂A Γ∋x⦂B = lookup-unique {Γ} x Γ∋x⦂A Γ∋x⦂B

uniqueness : ∀ {Γ Σ gc gc† pc pc† A B M}
  → Γ ; Σ ; gc  ; pc  ⊢ M ⦂ A
  → Γ ; Σ ; gc† ; pc† ⊢ M ⦂ B
    -----------------------------------
  → A ≡ B
uniqueness ⊢const ⊢const = refl
uniqueness (⊢addr eq) (⊢addr eq†) =
  case trans (sym eq) eq† of λ where
  refl → refl
uniqueness {Γ} (⊢var {x = x} ∋x) (⊢var ∋x†) =
  lookup-unique {Γ} x ∋x ∋x†
uniqueness (⊢lam ⊢N) (⊢lam ⊢N†) =
  case uniqueness {pc = low} {low} ⊢N ⊢N† of λ where
  refl → refl
uniqueness {gc = gc} {gc†} (⊢app {g = g} ⊢L ⊢M) (⊢app {g = g†} ⊢L† ⊢M†)
  with gc ⋎̃ g | gc† ⋎̃ g† | uniqueness ⊢L ⊢L†
... | ⋆   | ⋆    | refl = refl
... | l ℓ | l .ℓ | refl = refl
uniqueness (⊢if ⊢L ⊢M ⊢N) (⊢if ⊢L† ⊢M† ⊢N†) =
  case uniqueness ⊢L ⊢L† of λ where
  refl → refl
uniqueness (⊢let ⊢M ⊢N) (⊢let ⊢M† ⊢N†) =
  case uniqueness ⊢M ⊢M† of λ where
  refl → uniqueness {pc = low} {low} ⊢N ⊢N†
uniqueness (⊢ref ⊢M _) (⊢ref ⊢M† _) =
  cong (λ □ → Ref □ of l low) (uniqueness ⊢M ⊢M†)
uniqueness (⊢ref? ⊢M) (⊢ref? ⊢M†) =
  cong (λ □ → Ref □ of l low) (uniqueness ⊢M ⊢M†)
uniqueness (⊢ref✓ ⊢M _) (⊢ref✓ ⊢M† _) =
  cong (λ □ → Ref □ of l low) (uniqueness ⊢M ⊢M†)
uniqueness (⊢deref ⊢M) (⊢deref ⊢M†) =
  case uniqueness ⊢M ⊢M† of λ where
  refl → refl
uniqueness (⊢assign ⊢L ⊢M x) (⊢assign ⊢L† ⊢M† _) = refl
uniqueness (⊢assign? ⊢L ⊢M) (⊢assign? ⊢L† ⊢M†) = refl
uniqueness (⊢assign✓ ⊢L ⊢M _) (⊢assign✓ ⊢L† ⊢M† _) = refl
uniqueness (⊢prot ⊢M) (⊢prot ⊢M†) =
  cong (λ □ → stamp □ _) (uniqueness ⊢M ⊢M†)
uniqueness (⊢cast ⊢M) (⊢cast ⊢M†) = refl
uniqueness (⊢cast-pc ⊢M _) (⊢cast-pc ⊢M† _) = uniqueness ⊢M ⊢M†
uniqueness ⊢err ⊢err = refl
uniqueness (⊢sub ⊢M) (⊢sub ⊢M†) = refl
uniqueness (⊢sub-pc ⊢M x) ⊢M† = uniqueness ⊢M ⊢M†
uniqueness ⊢M (⊢sub-pc ⊢M† x) = uniqueness ⊢M ⊢M†
