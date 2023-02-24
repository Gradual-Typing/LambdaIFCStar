module CC.Catchup where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC.CCStatics
open import CC.Reduction
open import CC.MultiStep

open import Simulator.AST
open import Simulator.CheckPrecision

-- cc-prec→⊑ : ∀ {Σ Σ′ gc gc′ pc pc′ A A′ M M′}
--   → (⊢M : [] ; Σ ; gc ; pc ⊢ M ⦂ A)
--   → (⊢M′ : [] ; Σ′ ; gc′ ; pc′ ⊢ M′ ⦂ A′)
--   → check-⊑? (to-ast M ⊢M A) (to-ast M′ ⊢M′ A′) ≡ true
--   → A ⊑ A′

sub-val-left : ∀ {Σ Σ′ gc gc′ pc pc′ A A′ B′ M V′}
  → (⊢M  : [] ; Σ  ; gc  ; pc  ⊢ M  ⦂ A )
  → (⊢V′ : [] ; Σ′ ; gc′ ; pc′ ⊢ V′ ⦂ A′)
  → Value V′
  → (A′<:B′ : A′ <: B′)
  → check-⊑? (to-ast M ⊢M A) (to-ast V′ (⊢sub ⊢V′ A′<:B′) B′) ≡ true
    ----------------------------------------------------------------------
  → check-⊑? (to-ast M ⊢M A) (to-ast V′ ⊢V′ A′) ≡ true
sub-val-left ⊢M (⊢addr x) V-addr A′<:B′ eq = {!!}
sub-val-left ⊢M (⊢sub ⊢V′ x) V-addr A′<:B′ eq = {!!}
sub-val-left ⊢M (⊢sub-pc ⊢V′ gc<:gc′) V-addr A′<:B′ eq =
  sub-val-left ⊢M ⊢V′ V-addr A′<:B′ eq
sub-val-left ⊢M ⊢V′ V-ƛ A′<:B′ eq = {!!}
sub-val-left ⊢M ⊢V′ V-const A′<:B′ eq = {!!}
sub-val-left ⊢M ⊢V′ (V-cast v′ x) A′<:B′ eq = {!!}
sub-val-left ⊢M ⊢V′ V-● A′<:B′ eq = {!!}

catchup : ∀ {μ₁ Σ₁ Σ′ gc gc′ pc pc′ A A′ M V′}
  → (⊢M  : [] ; Σ₁ ; gc  ; pc  ⊢ M  ⦂ A )
  → (⊢V′ : [] ; Σ′ ; gc′ ; pc′ ⊢ V′ ⦂ A′)
  → Value V′
  → check-⊑? (to-ast M ⊢M A) (to-ast V′ ⊢V′ A′) ≡ true
    -------------------------------------------------------------------
  → ∃[ V ] ∃[ Σ₂ ] Σ[ ⊢V ∈ [] ; Σ₂ ; gc ; pc ⊢ V ⦂ A ] ∃[ μ₂ ]
      (Value V) × (M ∣ μ₁ ∣ pc —↠ V ∣ μ₂) × (check-⊑? (to-ast V ⊢V A) (to-ast V′ ⊢V′ A′) ≡ true)
catchup (⊢addr x₁) (⊢addr x) V-addr eq = {!!}
catchup (⊢sub ⊢M x₁) (⊢addr x) V-addr eq = {!!}
catchup (⊢sub-pc ⊢M x₁) (⊢addr x) V-addr eq = {!!}
catchup ⊢M ⊢V′ V-ƛ eq = {!!}
catchup ⊢M ⊢V′ V-const eq = {!!}
catchup ⊢M ⊢V′ (V-cast v′ x) eq = {!!}
catchup ⊢M ⊢V′ V-● eq = {!!}
catchup (⊢cast ⊢M) ⊢V′ v′ eq = {!!}
catchup (⊢cast-pc ⊢M x₁) ⊢V′ v′ eq = {!!}
catchup ⊢M (⊢sub ⊢V′ A<:B) v′ eq₁ = {!!}
  -- let ⟨ V , Σ₂ , ⊢V , μ₂ , v , M↠V , eq₂ ⟩ = catchup ⊢M ⊢V′ v′ {!!} in
  -- {!!}
catchup ⊢M (⊢sub-pc ⊢V′ gc<:gc′) v′ eq = {!!}
