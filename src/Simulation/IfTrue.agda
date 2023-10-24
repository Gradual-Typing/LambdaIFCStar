module Simulation.IfTrue where

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
open import LabelExpr.Security
open import LabelExpr.Stamping
open import LabelExpr.CatchUpBack using (catchup-back-success)
open import LabelExpr.GG
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision
open import CC2.CatchUp
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

open import Simulation.SimCast


sim-if-true : ∀ {Σ Σ′ gc gc′} {M M′ N′ μ μ′ PC PC′} {A A′ B′} {ℓ}
    → (vc  : LVal PC)
    → (vc′ : LVal PC′)
    → let ℓv  = ∥ PC  ∥ vc  in
       let ℓv′ = ∥ PC′ ∥ vc′ in
       [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ if ($ true) B′ ℓ M′ N′ ⇐ A ⊑ A′
    → Σ ⊑ₘ Σ′
    → Σ ; Σ′ ⊢ μ ⊑ μ′
    → PC ⊑ PC′ ⇐ gc ⊑ gc′
    → SizeEq μ μ′
      --------------------------------------------------------------------------
    → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
              [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
                     N ⊑ prot (stampₑ PC′ vc′ ℓ) (stampₑ-LVal vc′) ℓ M′ B′
                  ⇐ A ⊑ A′
sim-if-true {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-if {ℓc = ℓc} {L = L} {L′} {M} {M′} {N} {N′} {ℓ = ℓ} L⊑L′ M⊑M′ N⊑N′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq = ?
sim-if-true {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-if!l {ℓc = ℓc} {L = L} {L′} {M} {M′} {N} {N′} {ℓ = ℓ} L⊑L′ M⊑M′ N⊑N′ eq eq′)
    Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq = ?
sim-if-true vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq =
  case sim-if-true vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq of λ where
  ⟨ N , M↠N , N⊑N′ ⟩ →
    ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
