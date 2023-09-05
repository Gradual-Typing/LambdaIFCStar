{-# OPTIONS --allow-unsolved-metas #-} -- FIXME


module CC2.Simulation.AssignCast where

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
open import CC2.SimCast
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)


sim-assign-cast : ∀ {Σ Σ′ gc gc′} {M V′ W′ μ₁ μ₁′ PC PC′} {A A′ S T n ℓ₁ ℓ₂ ℓ̂₁ ℓ̂₂}
               {c̅ : CExpr l ℓ₁ ⇒ l ℓ₂} {c : Cast T of l ℓ̂₂ ⇒ S of l ℓ̂₁} {d : Cast S of l ℓ̂₁ ⇒ T of l ℓ̂₂}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ assign (addr n ⟨ cast (ref c d) c̅ ⟩) V′ T ℓ̂₂ ℓ₂ ⇐ A ⊑ A′
  → Σ ⊑ₘ Σ′
  → Σ ; Σ′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ₁ μ₁′
  → (v′ : Value V′)
  → (𝓋′ : CVal c̅)
  → V′ ⟨ c ⟩ —↠ W′
  → (w′ : Value W′)
    -------------------
  → let μ₂′ = cons-μ (a⟦ ℓ̂₁ ⟧ n) W′ w′ μ₁′ in
     ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ $ tt ⇐ A ⊑ A′) ×
       (Σ ; Σ′ ⊢ μ₂ ⊑ μ₂′) ×
       (SizeEq μ₂ μ₂′)
sim-assign-cast {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-assign L⊑L′ M⊑V′ ℓc≼ℓ̂ ℓ≼ℓ̂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′ = {!!}
sim-assign-cast {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-assign?l L⊑L′ M⊑V′ ℓc≼ℓ̂ ℓ≼ℓ̂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′ = {!!}
sim-assign-cast {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′
  with sim-assign-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′
... | ⟨ N , μ , M↠N , N⊑N′ , μ⊑μ′ , size-eq′ ⟩ =
  ⟨ N ⟨ c ⟩ , μ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ⊑μ′ , size-eq′ ⟩
