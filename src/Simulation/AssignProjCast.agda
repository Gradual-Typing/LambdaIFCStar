module Simulation.AssignProjCast where

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
open import Simulation.CatchUp
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

open import Simulation.SimCast


sim-assign?-cast : ∀ {Σ Σ′ gc gc′} {M V′ W′ μ₁ μ₁′ PC PC′ PC″} {A A′ S T ĝ n ℓ ℓ̂ p}
                     {c̅ₙ : CExpr l ℓ ⇒ ⋆} {c : Cast T of ĝ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of ĝ}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ assign? (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V′ T ĝ p ⇐ A ⊑ A′
  → Σ ⊑ₘ Σ′
  → Σ ; Σ′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ₁ μ₁′
  → (v′ : Value V′)
  → (𝓋′ : CVal c̅ₙ)
  → stamp!ₑ PC′ vc′ (∥ c̅ₙ ∥ₗ 𝓋′) ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ PC″
  → LVal PC″
  → V′ ⟨ c ⟩ —↠ W′
  → (w′ : Value W′)
    -------------------------------------------------------
  → let μ₂′ = cons-μ (a⟦ ℓ̂ ⟧ n) W′ w′ μ₁′ in
     ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ $ tt ⇐ A ⊑ A′) ×
       (Σ ; Σ′ ⊢ μ₂ ⊑ μ₂′) ×
       (SizeEq μ₂ μ₂′)
sim-assign?-cast {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-assign? L⊑L′ M⊑V′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′
  with catchup {μ = μ} {PC} (V-cast V-addr (ir-ref 𝓋′)) L⊑L′
... | ⟨ V , v , L↠V , prec1 ⟩
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ W , w , M↠W , prec2 ⟩
  with v | prec1
... | V-cast V-addr (ir-ref 𝓋)
    | ⊑-cast (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) =
  let ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
  let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
        (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
         (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
    size-eq-cons {v = w₁} {w′} {n} {ℓ} size-eq ⟩
... | V-cast V-addr (ir-ref 𝓋)
    | ⊑-castl (⊑-castr (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref A⊑c′ A⊑d′ ℓ⊑c̅′)) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  let c̅⊑c̅′ = comp-pres-⊑-rl ℓ⊑c̅′ c̅⊑g′
      ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
  let c⊑c′ = comp-pres-prec-lr c⊑A′ A⊑c′ in
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
  let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
        (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
         (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
    size-eq-cons {v = w₁} {w′} {n} {ℓ} size-eq ⟩
... | V-cast V-addr (ir-ref 𝓋)
    | ⊑-castr (⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑ℓ)) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) =
  let c̅⊑c̅′ = comp-pres-⊑-lr c̅⊑ℓ g⊑c̅′
      ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
  let c⊑c′ = comp-pres-prec-rl A⊑c′ c⊑A′ in
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
  let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
        (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
         (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
    size-eq-cons {v = w₁} {w′} {n} {ℓ} size-eq ⟩
sim-assign?-cast {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′
  with sim-assign?-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′
... | ⟨ N , μ , M↠N , N⊑N′ , μ⊑μ′ , size-eq′ ⟩ =
  ⟨ N ⟨ c ⟩ , μ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ⊑μ′ , size-eq′ ⟩
