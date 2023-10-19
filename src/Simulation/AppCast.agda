module Simulation.AppCast where

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


postulate
  sim-app-cast : ∀ {Σ Σ′ gc gc′} {M N′ V′ W′ μ μ′ PC PC′ PC″} {A A′ B′ C′ D′ E′} {ℓ₁ ℓ₂ g₁ g₂}
                   {c : Cast D′ ⇒ B′} {d : Cast C′ ⇒ E′} {d̅ : CExpr g₂ ⇒ g₁} {c̅ : CExpr l ℓ₁ ⇒ l ℓ₂}
    → (vc  : LVal PC)
    → (vc′ : LVal PC′)
    → let ℓv  = ∥ PC  ∥ vc  in
       let ℓv′ = ∥ PC′ ∥ vc′ in
       [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ app (ƛ N′ ⟨ cast (fun d̅ c d) c̅ ⟩) V′ D′ E′ ℓ₂ ⇐ A ⊑ A′
    → Σ ⊑ₘ Σ′
    → Σ ; Σ′ ⊢ μ ⊑ μ′
    → PC ⊑ PC′ ⇐ gc ⊑ gc′
    → SizeEq μ μ′
    → Value V′
    → (𝓋′ : CVal c̅)
    → (stampₑ PC′ vc′ ℓ₂) ⟪ d̅ ⟫ —↠ₑ PC″
    → (vc″ : LVal PC″)
    → V′ ⟨ c ⟩ —↠ W′
    → Value W′
      --------------------------------------------------------------------------
    → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
              [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
                     N ⊑ prot PC″ vc″ ℓ₂ ((N′ [ W′ ]) ⟨ d ⟩) E′
                  ⇐ A ⊑ A′
