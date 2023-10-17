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
open import CoercionExpr.CoercionExpr using (det-mult; success; fail)
open import CoercionExpr.Precision
  using (coerce⇒⋆-prec; ⊑-right-contract; ⊑-right-expand; ⊑-left-contract; ⊑-left-expand)
open import CoercionExpr.SyntacComp
open import CoercionExpr.GG renaming (catchup to catchupₗ; catchup-back to catchupₗ-back)
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
sim-cast-step {μ = μ} {PC = PC} vc vc′ (⊑-cast M⊑V′ c⊑c′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (V-raw _) (cast v′ c̅′→⁺c̅ₙ 𝓋′) =
  case catchup {μ = μ} {PC = PC} (V-raw v′) M⊑V′ of λ where
  ⟨ _ , V-raw v , M↠V , V⊑V′ ⟩ →
    case ⟨ c⊑c′ , V⊑V′ ⟩ of λ where
    ⟨ ⊑-base c̅⊑c̅′ , ⊑-const ⟩ →
      case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) of λ where
      ⟨ c̅ₙ , id , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                         _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) CVal.id) ⟩
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                        _ ∣ _ ∣ _ ∎) ,
          ⊑-castr ⊑-const (⊑-base (⊑-right-contract c̅ₙ⊑c̅ₙ′)) ⟩
      ⟨ c̅ₙ , up id , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                       _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) (up CVal.id)) ⟩
                       _ ∣ _ ∣ _ ∎) ,
          ⊑-cast ⊑-const (⊑-base c̅ₙ⊑c̅ₙ′) ⟩
      ⟨ c̅ₙ , inj 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                       _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋)) ⟩
                       _ ∣ _ ∣ _ ∎) ,
          ⊑-cast ⊑-const (⊑-base c̅ₙ⊑c̅ₙ′) ⟩
    ⟨ ⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′ , ⊑-addr a b ⟩ →
      case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) of λ where
      ⟨ c̅ₙ , 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-addr) (cast V-addr (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                        _ ∣ _ ∣ _ ∎) ,
          ⊑-cast (⊑-addr a b) (⊑-ref c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ⟩
    ⟨ ⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ , ⊑-lam gc⊑gc′ A⊑A′ N⊑N′ ⟩ →
      case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) of λ where
      ⟨ c̅ₙ , 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-ƛ) (cast V-ƛ (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                        _ ∣ _ ∣ _ ∎) ,
          ⊑-cast (⊑-lam gc⊑gc′ A⊑A′ N⊑N′)
                 (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ⟩
  ⟨ _ , V-cast v i , M↠V , ⊑-castl V⊑V′ c₁⊑A′ ⟩ →
    case ⟨ c₁⊑A′ ,  c⊑c′ , V⊑V′ ⟩ of λ where
    ⟨ ⊑-base c̅₁⊑g′ , ⊑-base c̅⊑c̅′ , ⊑-const ⟩ →
      case sim-mult (comp-pres-⊑-lb c̅₁⊑g′ c̅⊑c̅′) 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) of λ where
      ⟨ c̅ₙ , id , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (_ ∣ _ ∣ _ —→⟨ cast (V-cast V-const i) (cast-comp V-const i) ⟩
                      _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (comp-→⁺ ↠c̅ₙ CVal.id) CVal.id) ⟩
                      _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                      _ ∣ _ ∣ _ ∎) ,
          ⊑-castr ⊑-const (⊑-base (⊑-right-contract c̅ₙ⊑c̅ₙ′)) ⟩
      ⟨ c̅ₙ , up id , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (_ ∣ _ ∣ _ —→⟨ cast (V-cast V-const i) (cast-comp V-const i) ⟩
                      _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (comp-→⁺ ↠c̅ₙ (up CVal.id)) (up CVal.id)) ⟩
                      _ ∣ _ ∣ _ ∎) ,
          ⊑-cast ⊑-const (⊑-base c̅ₙ⊑c̅ₙ′) ⟩
      ⟨ c̅ₙ , inj 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (_ ∣ _ ∣ _ —→⟨ cast (V-cast V-const i) (cast-comp V-const i) ⟩
                      _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (comp-→⁺ ↠c̅ₙ (inj 𝓋)) (inj 𝓋)) ⟩
                      _ ∣ _ ∣ _ ∎) ,
          ⊑-cast ⊑-const (⊑-base c̅ₙ⊑c̅ₙ′) ⟩
    ⟨ ⊑-ref c₁⊑A′ d₁⊑A′ c̅₁⊑g′ , ⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′ , ⊑-addr a b ⟩ →
      case sim-mult (comp-pres-⊑-lb c̅₁⊑g′ c̅⊑c̅′) 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) of λ where
      ⟨ c̅ₙ , 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (_ ∣ _ ∣ _ —→⟨ cast (V-cast V-addr i) (cast-comp V-addr i) ⟩
                      _ ∣ _ ∣ _ —→⟨ cast (V-raw V-addr) (cast V-addr (comp-→⁺ ↠c̅ₙ 𝓋) 𝓋) ⟩
                      _ ∣ _ ∣ _ ∎) ,
          ⊑-cast (⊑-addr a b) (⊑-ref (comp-pres-prec-bl c⊑c′ c₁⊑A′) (comp-pres-prec-lb d₁⊑A′ d⊑d′) c̅ₙ⊑c̅ₙ′) ⟩
    ⟨ ⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ , ⊑-lam gc⊑gc′ A⊑A′ N⊑N′ ⟩ →
      case sim-mult (comp-pres-⊑-lb c̅₁⊑g′ c̅⊑c̅′) 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) of λ where
      ⟨ c̅ₙ , 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                     (_ ∣ _ ∣ _ —→⟨ cast (V-cast V-ƛ i) (cast-comp V-ƛ i) ⟩
                      _ ∣ _ ∣ _ —→⟨ cast (V-raw V-ƛ) (cast V-ƛ (comp-→⁺ ↠c̅ₙ 𝓋) 𝓋) ⟩
                      _ ∣ _ ∣ _ ∎) ,
          ⊑-cast (⊑-lam gc⊑gc′ A⊑A′ N⊑N′)
                 (⊑-fun (comp-pres-⊑-bl d̅⊑d̅′ d̅₁⊑gc′)
                        (comp-pres-prec-bl c⊑c′ c₁⊑A′)
                        (comp-pres-prec-lb d₁⊑B′ d⊑d′) c̅ₙ⊑c̅ₙ′) ⟩
  ⟨ _ , V-● , M↠● , ●⊑V′ ⟩ → contradiction ●⊑V′ (●⋤ _)
sim-cast-step {μ = μ} {PC = PC} vc vc′ (⊑-castr M⊑V′ A⊑c′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast vᵣ′ c̅′→⁺c̅ₙ′ 𝓋′) =
  case catchup {μ = μ} {PC = PC} v′ M⊑V′ of λ where
  ⟨ _ , V-raw v , M↠V , V⊑V′ ⟩ →
    case ⟨ A⊑c′ , V⊑V′ ⟩ of λ where
    ⟨ ⊑-base g⊑c̅′ , ⊑-const ⟩ →
      let id⊑c̅′ = ⊑-right-expand g⊑c̅′ in
      case catchupₗ-back _ _ CVal.id id⊑c̅′ of λ where
      ⟨ _ , ↠c̅ₙ′ , v-v 𝓋† id⊑c̅ₙ′ ⟩ →
        case det-mult ↠c̅ₙ′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) (success 𝓋†) (success 𝓋′) of λ where
        refl → ⟨ _ , M↠V , ⊑-castr V⊑V′ (⊑-base (⊑-right-contract id⊑c̅ₙ′)) ⟩
      ⟨ _ , ↠⊥ , v-⊥ _ ⟩ →
        case det-mult ↠⊥ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) fail (success 𝓋′) of λ where
        refl → case 𝓋′ of λ where ()
    ⟨ ⊑-ref A⊑c′ A⊑d′ g⊑c̅′ , ⊑-addr _ _ ⟩ →
      let id⊑c̅′ = ⊑-right-expand g⊑c̅′ in
      case catchupₗ-back _ _ CVal.id id⊑c̅′ of λ where
      ⟨ _ , ↠c̅ₙ′ , v-v 𝓋† id⊑c̅ₙ′ ⟩ →
        case det-mult ↠c̅ₙ′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) (success 𝓋†) (success 𝓋′) of λ where
        refl → ⟨ _ , M↠V , ⊑-castr V⊑V′ (⊑-ref A⊑c′ A⊑d′ (⊑-right-contract id⊑c̅ₙ′)) ⟩
      ⟨ _ , ↠⊥ , v-⊥ _ ⟩ →
        case det-mult ↠⊥ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) fail (success 𝓋′) of λ where
        refl → case 𝓋′ of λ where ()
    ⟨ ⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′ , ⊑-lam _ _ _ ⟩ →
      let id⊑c̅′ = ⊑-right-expand g⊑c̅′ in
      case catchupₗ-back _ _ CVal.id id⊑c̅′ of λ where
      ⟨ _ , ↠c̅ₙ′ , v-v 𝓋† id⊑c̅ₙ′ ⟩ →
        case det-mult ↠c̅ₙ′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) (success 𝓋†) (success 𝓋′) of λ where
        refl → ⟨ _ , M↠V , ⊑-castr V⊑V′ (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ (⊑-right-contract id⊑c̅ₙ′)) ⟩
      ⟨ _ , ↠⊥ , v-⊥ _ ⟩ →
        case det-mult ↠⊥ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) fail (success 𝓋′) of λ where
        refl → case 𝓋′ of λ where ()
  ⟨ _ , V-cast v i , M↠V , ⊑-castl V⊑V′ c₁⊑A′ ⟩ →
    case ⟨ comp-pres-prec-lr c₁⊑A′ A⊑c′ , V⊑V′ ⟩ of λ where
    ⟨ ⊑-base c̅⊑c̅′ , ⊑-const ⟩ →
      case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) of λ where
      ⟨ c̅ₙ , id , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult M↠V
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                         _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) CVal.id) ⟩
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                        _ ∣ _ ∣ _ ∎) ,
          ⊑-castr ⊑-const (⊑-base (⊑-right-contract c̅ₙ⊑c̅ₙ′)) ⟩
      ⟨ c̅ₙ , up id , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult M↠V
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                       _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) (up CVal.id)) ⟩
                       _ ∣ _ ∣ _ ∎) ,
          ⊑-cast ⊑-const (⊑-base c̅ₙ⊑c̅ₙ′) ⟩
      ⟨ c̅ₙ , inj 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult M↠V
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                       _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋)) ⟩
                       _ ∣ _ ∣ _ ∎) ,
          ⊑-cast ⊑-const (⊑-base c̅ₙ⊑c̅ₙ′) ⟩
    ⟨ ⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′ , ⊑-addr a b ⟩ →
      case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) of λ where
      ⟨ c̅ₙ , 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult M↠V
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-addr) (cast V-addr (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                        _ ∣ _ ∣ _ ∎) ,
          ⊑-cast (⊑-addr a b) (⊑-ref c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ⟩
    ⟨ ⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ , ⊑-lam gc⊑gc′ A⊑A′ N⊑N′ ⟩ →
      case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) of λ where
      ⟨ c̅ₙ , 𝓋 , ↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
        ⟨ _ ,
          trans-mult M↠V
                     (case ↠c̅ₙ of λ where
                      (_ ∎ₗ) → _ ∣ _ ∣ _ ∎
                      (_ —→ₗ⟨ r ⟩ r*) →
                        _ ∣ _ ∣ _ —→⟨ cast (V-raw V-ƛ) (cast V-ƛ (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                        _ ∣ _ ∣ _ ∎) ,
          ⊑-cast (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ⟩
  ⟨ _ , V-● , M↠● , ●⊑V′ ⟩ → contradiction ●⊑V′ (●⋤ _)
sim-cast-step vc vc′ prec Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast-blame vᵣ c̅↠⊥) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ prec in
  ⟨ _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ ⟩
sim-cast-step {μ = μ} {PC = PC} vc vc′ (⊑-cast prec (⊑-base c̅⊑id)) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ cast-id =
  case catchup {μ = μ} {PC = PC} v′ prec of λ where
  ⟨ _ , _ , M↠V , V⊑V′ ⟩ → ⟨ _ , plug-cong □⟨ _ ⟩ M↠V , ⊑-castl V⊑V′ (⊑-base (⊑-left-contract c̅⊑id)) ⟩
sim-cast-step {μ = μ} {PC = PC} vc vc′ (⊑-castr prec A⊑c′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ cast-id =
  case catchup {μ = μ} {PC = PC} v′ prec of λ where
  ⟨ _ , _ , M↠V , V⊑V′ ⟩ → ⟨ _ , M↠V , V⊑V′ ⟩
sim-cast-step {μ = μ} {PC = PC} vc vc′ (⊑-cast prec c⊑c′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast-comp vᵣ′ i′) =
  case catchup {μ = μ} {PC = PC} (V-cast vᵣ′ i′) prec of λ where
  ⟨ _ , V-raw v , M↠V , ⊑-castr V⊑V′ A⊑cᵢ′ ⟩ →
    ⟨ _ , plug-cong □⟨ _ ⟩ M↠V , ⊑-cast V⊑V′ (comp-pres-prec-rb A⊑cᵢ′ c⊑c′) ⟩
  ⟨ _ , V-cast vᵣ i , M↠V , V⊑V′ ⟩ →
    case cast-prec-inv V⊑V′ vᵣ vᵣ′ of λ where
    ⟨ W⊑W′ , cᵢ⊑cᵢ′ , refl , refl ⟩ →
      ⟨ _ ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast vᵣ i) (cast-comp vᵣ i) ⟩ _ ∣ _ ∣ _ ∎) ,
        ⊑-cast W⊑W′ (comp-pres-prec cᵢ⊑cᵢ′ c⊑c′) ⟩
  ⟨ _ , V-● , M↠● , ●⊑V′ ⟩ → contradiction ●⊑V′ (●⋤ _)
sim-cast-step {μ = μ} {PC = PC} vc vc′ (⊑-castr prec A⊑c′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ (cast-comp vᵣ′ i′) =
  case catchup {μ = μ} {PC = PC} (V-cast vᵣ′ i′) prec of λ where
  ⟨ _ , V-raw v , M↠V , ⊑-castr V⊑V′ A⊑cᵢ′ ⟩ →
    ⟨ _ , M↠V , ⊑-castr V⊑V′ (comp-pres-prec-rr A⊑cᵢ′ A⊑c′) ⟩
  ⟨ _ , V-cast vᵣ i , M↠V , V⊑V′ ⟩ →
    case cast-prec-inv V⊑V′ vᵣ vᵣ′ of λ where
    ⟨ W⊑W′ , cᵢ⊑cᵢ′ , refl , refl ⟩ →
      ⟨ _ ,
        M↠V ,
        ⊑-cast W⊑W′ (comp-pres-prec-br cᵢ⊑cᵢ′ A⊑c′) ⟩
  ⟨ _ , V-● , M↠● , ●⊑V′ ⟩ → contradiction ●⊑V′ (●⋤ _)
sim-cast-step vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ r =
  case sim-cast-step vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ r of λ where
  ⟨ N , M↠N , N⊑N′ ⟩ →
    ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
