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
open import LabelExpr.Security
open import LabelExpr.Stamping
open import LabelExpr.CatchUpBack using (catchup-back-success)
open import LabelExpr.GG
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision
open import Simulation.CatchUp
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

open import Simulation.SimCast


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
sim-app-cast {Σ} {Σ′} {.(l _)} {.(l _)} {μ = μ} {PC = PC} {PC′} {ℓ₁ = ℓ₁} {ℓ₂} {g₁} {g₂} vc vc′
  (⊑-app L⊑L′ M⊑V′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ =
  case catchup {μ = μ} {PC} v′ M⊑V′ of λ where
  ⟨ W , w , M↠W , W⊑V′ ⟩ →
    let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
    case catchup {μ = μ} {PC} (V-cast V-ƛ (ir-fun 𝓋′)) L⊑L′ of λ where
    ⟨ V , v , L↠V , prec ⟩ →
      case ⟨ v , prec ⟩ of λ where
      ⟨ V-raw V-ƛ , ⊑-castr (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′) ⟩ →
        let W⊑W′ = sim-cast-right W⊑V′ w v′ A⊑c′ ↠W′ w′ in
        let ♣ = trans-mult (plug-cong (app□ _ _ _ _) L↠V)
                           (trans-mult (plug-cong (app _ □ (V-raw V-ƛ) _ _ _) M↠W)
                           (_ ∣ _ ∣ _ —→⟨ β w vc ⟩ _ ∣ _ ∣ _ ∎)) in
        let N[W]⊑N′[W′] = substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W⊑W′ w w′) in
        let stampPC⊑PC″ = catchup-back-success (stampₑ-LVal vc) (⊑-castr (stampₑ-prec vc vc′ PC⊑PC′) gc⊑d̅′) ↠PC″ vc″ in
        ⟨ _ , ♣ ,
          ⊑-prot (⊑-castr N[W]⊑N′[W′] B⊑d′) stampPC⊑PC″
                 (≡→≼ (stampₑ-security vc)) (stamp-cast-security vc′ ⊢PC′ ↠PC″ vc″) eq eq′ ⟩
      ⟨ V-cast v i , prec ⟩ →
        case ⟨ v , cast-prec-inv prec v V-ƛ ⟩ of λ where
        ⟨ V-ƛ , ⊑-lam gc⊑gc′ A⊑A′ N⊑N′ , c⊑c′ , refl , refl ⟩ →
          case ⟨ i , c⊑c′ ⟩ of λ where
          ⟨ ir-fun {c = c} {d} {c̅} {d̅} 𝓋 , ⊑-fun {d̅′ = d̅′} {c̅′ = c̅′} d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ ⟩ →
            let ⟨ PC₁ , vc₁ , ↠PC₁ , pc-prec′ ⟩ = sim-mult (⊑-cast (stampₑ-prec vc vc′ PC⊑PC′) d̅⊑d̅′) ↠PC″ vc″ in
            let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast W⊑V′ w v′ c⊑c′ ↠W′ w′ in
            let ♣ = trans-mult (plug-cong (app□ _ _ _ _) L↠V)
                    (trans-mult (plug-cong (app _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _ _) M↠W)
                    (_ ∣ _ ∣ _ —→⟨ app-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
            ⟨ _ , ♣ ,
              ⊑-prot (⊑-cast (substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑W′ w₁ w′)) d⊑d′)
                pc-prec′ (stamp-cast-security vc ⊢PC ↠PC₁ vc₁)
                (stamp-cast-security vc′ ⊢PC′ ↠PC″ vc″)
                eq eq′ ⟩
      ⟨ V-● , ●⊑ ⟩ → contradiction ●⊑ (●⋤ _)
sim-app-cast {Σ} {Σ′} {gc} {.(l _)} {μ = μ} {PC = PC} {PC′} {ℓ₁ = ℓ₁} {ℓ₂} {g₁} {g₂} vc vc′
  (⊑-app!l L⊑L′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ =
  case catchup {μ = μ} {PC} v′ M⊑M′ of λ where
  ⟨ W , w , M↠W , W⊑M′ ⟩ →
    let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
    case catchup {μ = μ} {PC} (V-cast V-ƛ (ir-fun 𝓋′)) L⊑L′ of λ where
    ⟨ V , v , L↠V , prec ⟩ →
      case ⟨ v , prec ⟩ of λ where
      ⟨ V-raw V-ƛ , ⊑-castr () _ ⟩
      ⟨ V-cast v i , prec ⟩ →
        case ⟨ v , cast-prec-inv prec v V-ƛ ⟩ of λ where
        ⟨ V-ƛ , ⊑-lam gc⊑gc′ A⊑A′ N⊑N′ , c⊑c′ , refl , refl ⟩ →
          case ⟨ i , c⊑c′ ⟩ of λ where
          ⟨ ir-fun {c = c} {d} {c̅} {d̅} 𝓋 , ⊑-fun {d̅′ = d̅′} {c̅′ = c̅′} d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ ⟩ →
            let ∣c̅∣≼∣c̅′∣ : ∥ c̅ ∥ₗ 𝓋 ≼ ∥ c̅′ ∥ₗ 𝓋′
                ∣c̅∣≼∣c̅′∣ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′
                ∣c̅∣≼ℓ₂ : ∥ c̅ ∥ₗ 𝓋 ≼ ℓ₂
                ∣c̅∣≼ℓ₂ = subst (λ □ → _ ≼ □) (static-security _ 𝓋′) ∣c̅∣≼∣c̅′∣ in
            let pc-prec : (stamp!ₑ PC vc (∥ c̅ ∥ₗ 𝓋) ⟪ d̅ ⟫) ⊑ (stampₑ PC′ vc′ ℓ₂ ⟪ d̅′ ⟫) ⇐ _ ⊑ g₁
                pc-prec = ⊑-cast (stamp!ₑ-left-prec vc vc′ PC⊑PC′ ∣c̅∣≼ℓ₂) d̅⊑d̅′ in
            let ⟨ PC₁ , vc₁ , ↠PC₁ , pc-prec′ ⟩ = sim-mult pc-prec ↠PC″ vc″ in
            let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast W⊑M′ w v′ c⊑c′ ↠W′ w′ in
            let ♣ = trans-mult (plug-cong (app!□ _ _ _) L↠V)
                    (trans-mult (plug-cong (app! _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _) M↠W)
                    (_ ∣ _ ∣ _ —→⟨ app!-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
            ⟨ _ , ♣ ,
              ⊑-prot!l (⊑-cast (substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑W′ w₁ w′)) d⊑d′)
                pc-prec′ (stamp!-cast-security vc ⊢PC ↠PC₁ vc₁)
                (stamp-cast-security vc′ ⊢PC′ ↠PC″ vc″)
                eq eq′ ∣c̅∣≼ℓ₂ ⟩
      ⟨ V-● , ●⊑ ⟩ → contradiction ●⊑ (●⋤ _)
sim-app-cast vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ =
  case sim-app-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ of λ where
  ⟨ N , M↠N , N⊑N′ ⟩ →
    ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
