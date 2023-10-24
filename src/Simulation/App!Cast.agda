module Simulation.App!Cast where

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


sim-app!-cast : ∀ {Σ Σ′ gc gc′} {M N′ V′ W′ μ μ′ PC PC′ PC″} {A A′ B′ C′ D′ E′} {ℓ g}
                    {c : Cast D′ ⇒ B′} {d : Cast C′ ⇒ E′} {d̅ : CExpr ⋆ ⇒ g} {c̅ : CExpr l ℓ ⇒ ⋆}
    → (vc  : LVal PC)
    → (vc′ : LVal PC′)
    → let ℓv  = ∥ PC  ∥ vc  in
       let ℓv′ = ∥ PC′ ∥ vc′ in
       [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ app! (ƛ N′ ⟨ cast (fun d̅ c d) c̅ ⟩) V′ D′ E′ ⇐ A ⊑ A′
    → Σ ⊑ₘ Σ′
    → Σ ; Σ′ ⊢ μ ⊑ μ′
    → PC ⊑ PC′ ⇐ gc ⊑ gc′
    → SizeEq μ μ′
    → Value V′
    → (𝓋′ : CVal c̅)
    → let ℓ′ = ∥ c̅ ∥ₗ 𝓋′ in
       (stamp!ₑ PC′ vc′ ℓ′) ⟪ d̅ ⟫ —↠ₑ PC″
    → (vc″ : LVal PC″)
    → V′ ⟨ c ⟩ —↠ W′
    → Value W′
      --------------------------------------------------------------------------
    → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
              [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
                     N ⊑ prot! PC″ vc″ ℓ′ ((N′ [ W′ ]) ⟨ d ⟩) E′
                  ⇐ A ⊑ A′
sim-app!-cast {Σ} {Σ′} {μ = μ} {PC = PC} {PC′} {ℓ = ℓ} {g} vc vc′
  (⊑-app! L⊑L′ M⊑V′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ =
  {!!}
sim-app!-cast vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ =
  case sim-app!-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ of λ where
  ⟨ N , M↠N , N⊑N′ ⟩ →
    ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
