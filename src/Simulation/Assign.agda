module Simulation.Assign where

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


sim-assign : ∀ {Σ Σ′ gc gc′} {M V′ μ₁ μ₁′ PC PC′} {A A′ T n ℓ ℓ̂}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ assign (addr n) V′ T ℓ̂ ℓ ⇐ A ⊑ A′
  → Σ ⊑ₘ Σ′
  → Σ ; Σ′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ₁ μ₁′
  → (v′ : Value V′)
    --------------------------------------------------
  → let μ₂′ = cons-μ (a⟦ ℓ̂ ⟧ n) V′ v′ μ₁′ in
     ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ $ tt ⇐ A ⊑ A′) ×
       (Σ ; Σ′ ⊢ μ₂ ⊑ μ₂′) ×
       (SizeEq μ₂ μ₂′)
sim-assign {Σ} {Σ′} {.(l _)} {.(l _)} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-assign   L⊑L′ M⊑V′ ℓc≼ℓ̂ ℓ≼ℓ̂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
  with catchup {μ = μ} {PC} (V-raw V-addr) L⊑L′
... | ⟨ V , v , L↠V , prec1 ⟩
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ W , w , M↠W , prec2 ⟩
  with v | prec1  {- lhs can either be a cast or an address -}
... | V-raw V-addr | ⊑-addr {n = n} {ℓ̂ = ℓ} a b =
  let ♣ = trans-mult (plug-cong (assign□ _ _ _ _) L↠V)
          (trans-mult (plug-cong (assign _ □ (V-raw V-addr) _ _ _) M↠W)
          (_ ∣ _ ∣ _ —→⟨ β-assign w ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ _ , cons-μ _ W w _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc prec2 w v′) w v′ a b ,
    size-eq-cons {v = w} {v′} {n} {ℓ} size-eq ⟩
... | V-cast V-addr (ir-ref 𝓋) | ⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑ℓ) =
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑V′ ⟩ = sim-cast-left prec2 w v′ c⊑A′ in
  let ♣ = trans-mult (plug-cong (assign□ _ _ _ _) L↠V)
          (trans-mult (plug-cong (assign _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
          (_ ∣ _ ∣ _ —→⟨ assign-cast w 𝓋 ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑V′ w₁ v′) w₁ v′ a b ,
    size-eq-cons {v = w₁} {v′} {n} {ℓ} size-eq ⟩
sim-assign {Σ} {Σ′} {gc} {.(l _)} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-assign?l L⊑L′ M⊑V′ ℓc≼ℓ̂ ℓ≼ℓ̂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
  with catchup {μ = μ} {PC} (V-raw V-addr) L⊑L′
... | ⟨ V , v , L↠V , prec1 ⟩
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ W , w , M↠W , prec2 ⟩
  with v | prec1  {- lhs must be a cast -}
... | V-cast V-addr (ir-ref 𝓋)
    | ⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑ℓ) =
  let ∣c̅∣≡ℓ = security-prec-left _ 𝓋 c̅⊑ℓ in
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑V′ ⟩ = sim-cast-left prec2 w v′ c⊑A′ in
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign-left PC⊑PC′ vc vc′ ℓc≼ℓ̂ ℓ≼ℓ̂ in
  let ↠PC₁† = subst (λ □ → stamp!ₑ _ _ □ ⟪ _ ⟫ —↠ₑ _) (sym ∣c̅∣≡ℓ) ↠PC₁ in
  let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
          (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
          (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁† vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑V′ w₁ v′) w₁ v′ a b ,
    size-eq-cons {v = w₁} {v′} {n} {ℓ} size-eq ⟩
sim-assign {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
  with sim-assign vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
... | ⟨ N , μ , M↠N , N⊑N′ , μ⊑μ′ , size-eq′ ⟩ =
  ⟨ N ⟨ c ⟩ , μ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ⊑μ′ , size-eq′ ⟩
