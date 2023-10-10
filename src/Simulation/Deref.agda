module Simulation.Deref where

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

open import Simulation.Cast


sim-deref : ∀ {Σ Σ′ gc gc′} {M V′ μ μ′ PC PC′} {A A′ T n ℓ ℓ̂}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ ! (addr n) (T of l ℓ̂) ℓ ⇐ A ⊑ A′
  → Σ ⊑ₘ Σ′
  → Σ ; Σ′ ⊢ μ ⊑ μ′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ μ′
  → (v′ : Value V′)
  → lookup-μ μ′ (a⟦ ℓ̂ ⟧ n) ≡ just (V′ & v′)
    -------------------------------------------------------
  → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
            ([] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
              N ⊑ prot (l high) v-l ℓ V′ (T of l ℓ̂)
              ⇐ A ⊑ A′)
sim-deref {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-deref M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ μ′a≡V′
  with catchup {μ = μ} {PC} (V-raw V-addr) M⊑M′
... | ⟨ addr _ , V-raw V-addr , L↠V , ⊑-addr {n = n} {ℓ̂ = ℓ} a b ⟩ =
  let ⟨ _ , _ , V , v , V′ , v′ , μa≡V , μ′a≡V†′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ a b in
  case trans (sym μ′a≡V′) μ′a≡V†′ of λ where
  refl → ⟨ _ , trans-mult (plug-cong (!□ _ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref {v = v} μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
            ⊑-prot (value-⊑-pc V⊑V′ v v′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ ⟩
... | ⟨ addr _ ⟨ cast (ref c d) c̅ ⟩ , V-cast V-addr (ir-ref 𝓋) ,
        L↠V , ⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩ =
  let ⟨ _ , _ , V , v , V′ , v′ , μa≡V , μ′a≡V†′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ a b in
  case trans (sym μ′a≡V′) μ′a≡V†′ of λ where
  refl → ⟨ _ , trans-mult (plug-cong (!□ _ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref-cast {v = v} 𝓋 μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
            ⊑-prot (⊑-castl (value-⊑-pc V⊑V′ v v′) d⊑A′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ ⟩
sim-deref {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-deref!l M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ μ′a≡V′
  with catchup {μ = μ} {PC} (V-raw V-addr) M⊑M′
... | ⟨ addr _ , V-raw V-addr , L↠V , () ⟩
... | ⟨ addr _ ⟨ cast (ref c d) c̅ ⟩ , V-cast V-addr (ir-ref 𝓋) ,
        L↠V , ⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩ =
  let ⟨ _ , _ , V , v , V′ , v′ , μa≡V , μ′a≡V†′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ a b in
  case trans (sym μ′a≡V′) μ′a≡V†′ of λ where
  refl → ⟨ _ , trans-mult (plug-cong (!!□ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref!-cast {v = v} 𝓋 μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
            ⊑-prot!l (⊑-castl (value-⊑-pc V⊑V′ v v′) d⊑A′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ (≡→≼ (security-prec-left _ 𝓋 c̅⊑g′)) ⟩
sim-deref vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ x
  with sim-deref vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ x
... | ⟨ N , M↠N , N⊑N′ ⟩ =
  ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
