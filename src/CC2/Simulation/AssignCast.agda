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
open import CC2.CastSubtyping
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
                (⊑-assign L⊑L′ M⊑V′ ℓc≼ℓ̂ ℓ≼ℓ̂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ W , w , M↠W , W⊑V′ ⟩ =
  case catchup {μ = μ} {PC} (V-cast V-addr (ir-ref 𝓋′)) L⊑L′ of λ where
  ⟨ V , V-raw V-addr , L↠V , ⊑-castr (⊑-addr {n = n} {ℓ̂ = ℓ̂} a b) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) ⟩ →
    let ♣ = trans-mult (plug-cong (assign□ _ _ _ _) L↠V)
            (trans-mult (plug-cong (assign _ □ (V-raw V-addr) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ β-assign w ⟩ _ ∣ _ ∣ _ ∎)) in
    ⟨ _ , cons-μ _ W w _ , ♣ , ⊑-const ,
      ⊑μ-update μ⊑μ′ {!!} w w′ a b ,
      size-eq-cons {v = w} {w′} {n} {ℓ̂} size-eq ⟩
  ⟨ V , V-cast V-addr (ir-ref 𝓋) , L↠V , ⊑-cast (⊑-addr {n = n} {ℓ̂ = ℓ̂} a b) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) ⟩ →
    {!!}
  ⟨ V , V-cast V-addr (ir-ref 𝓋) , L↠V , ⊑-castl (⊑-castr (⊑-addr {n = n} {ℓ̂ = ℓ̂} a b) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′)) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩ →
    {!!}
  ⟨ V , V-cast V-addr (ir-ref 𝓋) , L↠V , ⊑-castr (⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ̂} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′)) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) ⟩ →
    {!!}
sim-assign-cast {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-assign?l L⊑L′ M⊑V′ ℓc≼ℓ̂ ℓ≼ℓ̂) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ W , w , M↠W , prec2 ⟩ =
  let ⟨ _ , ⊢V′ , _ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ prec2 in
  let ℓ̂≼ℓ̂₁ = cast-≼ v′ ⊢V′ ↠W′ w′ in
  case catchup {μ = μ} {PC} (V-cast V-addr (ir-ref 𝓋′)) L⊑L′ of λ where
  ⟨ V , V-raw V-addr , L↠V , ⊑-castr () _ ⟩
  ⟨ V , V-cast V-addr (ir-ref 𝓋) , L↠V , ⊑-cast (⊑-addr {n = n} {ℓ̂ = ℓ̂} a b) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) ⟩ →
    let ∣c̅∣≼∣c̅′∣ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
    let ∣c̅∣≼ℓ = subst (λ □ → _ ≼ □) (static-security _ 𝓋′) ∣c̅∣≼∣c̅′∣ in
    let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign-left PC⊑PC′ vc vc′ (≼-trans ℓc≼ℓ̂ ℓ̂≼ℓ̂₁) (≼-trans ∣c̅∣≼ℓ (≼-trans ℓ≼ℓ̂ ℓ̂≼ℓ̂₁)) in
    let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
    let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
            (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
    ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
      ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
      size-eq-cons {v = w₁} {w′} {n} {ℓ̂} size-eq ⟩
  ⟨ V , V-cast V-addr (ir-ref 𝓋) , L↠V , ⊑-castl (⊑-castr (⊑-addr {n = n} {ℓ̂ = ℓ̂} a b) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′)) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩ →
    let c̅⊑c̅′ = comp-pres-⊑-rl g⊑c̅′ c̅⊑g′ in
    let c⊑c′ = comp-pres-prec-lr c⊑A′ A⊑c′ in
    let ∣c̅∣≼∣c̅′∣ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
    let ∣c̅∣≼ℓ = subst (λ □ → _ ≼ □) (static-security _ 𝓋′) ∣c̅∣≼∣c̅′∣ in
    let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign-left PC⊑PC′ vc vc′ (≼-trans ℓc≼ℓ̂ ℓ̂≼ℓ̂₁) (≼-trans ∣c̅∣≼ℓ (≼-trans ℓ≼ℓ̂ ℓ̂≼ℓ̂₁)) in
    let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
    let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
            (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
    ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
      ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
      size-eq-cons {v = w₁} {w′} {n} {ℓ̂} size-eq ⟩
  ⟨ V , V-cast V-addr (ir-ref 𝓋) , L↠V , ⊑-castr (⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ̂} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′)) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) ⟩ →
    let c̅⊑c̅′ = comp-pres-⊑-lr c̅⊑g′ g⊑c̅′ in
    let c⊑c′ = comp-pres-prec-rl A⊑c′ c⊑A′ in
    let ∣c̅∣≼∣c̅′∣ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
    let ∣c̅∣≼ℓ = subst (λ □ → _ ≼ □) (static-security _ 𝓋′) ∣c̅∣≼∣c̅′∣ in
    let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign-left PC⊑PC′ vc vc′ (≼-trans ℓc≼ℓ̂ ℓ̂≼ℓ̂₁) (≼-trans ∣c̅∣≼ℓ (≼-trans ℓ≼ℓ̂ ℓ̂≼ℓ̂₁)) in
    let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
    let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
            (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
    ⟨ _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
      ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
      size-eq-cons {v = w₁} {w′} {n} {ℓ̂} size-eq ⟩
sim-assign-cast {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′
  with sim-assign-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠W′ w′
... | ⟨ N , μ , M↠N , N⊑N′ , μ⊑μ′ , size-eq′ ⟩ =
  ⟨ N ⟨ c ⟩ , μ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ⊑μ′ , size-eq′ ⟩
