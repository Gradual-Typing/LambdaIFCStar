module Simulation.Cast where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax
open import Common.Utils
open import Memory.HeapContext
open import CoercionExpr.Precision using (coerce⇒⋆-prec)
open import CoercionExpr.SyntacComp
open import LabelExpr.CatchUp renaming (catchup to catchupₑ)
open import LabelExpr.Security
open import LabelExpr.Stamping
open import LabelExpr.NSU
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision
open import CC2.CatchUp
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

open import Simulation.SimCast



sim-cast-step : ∀ {Σ Σ′ gc gc′} {M N′ V′ μ μ′ PC PC′} {A A′ B′ C′} {c′ : Cast B′ ⇒ C′}
    → (vc  : LVal PC)
    → (vc′ : LVal PC′)
    → let ℓv  = ∥ PC  ∥ vc  in
      let ℓv′ = ∥ PC′ ∥ vc′ in
      [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ V′ ⟨ c′ ⟩ ⇐ A ⊑ A′
    → Σ ⊑ₘ Σ′
    → Σ ; Σ′ ⊢ μ ⊑ μ′
    → PC ⊑ PC′ ⇐ gc ⊑ gc′
    → SizeEq μ μ′
    → Value V′
    → V′ ⟨ c′ ⟩ —→ N′
      --------------------------------------------------------------------------
    → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
            ([] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′)
sim-cast-step vc vc′ (⊑-cast prec x₃) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast x x₁ x₂) = {!!}
sim-cast-step vc vc′ (⊑-castr prec x₃) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast x x₁ x₂) = {!!}
sim-cast-step vc vc′ prec Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast-blame x x₁) = {!!}
sim-cast-step vc vc′ prec Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ cast-id = {!!}
sim-cast-step vc vc′ (⊑-cast prec x₂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast-comp x x₁) = {!!}
sim-cast-step vc vc′ (⊑-castr prec x₂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast-comp x x₁) = {!!}
sim-cast-step vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ r
  with sim-cast-step vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ r
... | ⟨ N , M↠N , N⊑N′ ⟩ =
  ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩

