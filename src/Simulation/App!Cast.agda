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
  let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
  case catchup {μ = μ} {PC} v′ M⊑V′ of λ where
  ⟨ W , w , M↠W , W⊑M′ ⟩ →
    case catchup {μ = μ} {PC} (V-cast V-ƛ (ir-fun 𝓋′)) L⊑L′ of λ where
    ⟨ V , v , L↠V , prec ⟩ →
      case ⟨ v , prec ⟩ of λ where
      ⟨ V-raw V-ƛ , ⊑-castr () _ ⟩
      ⟨ V-cast v i , prec ⟩ →
        case ⟨ v , cast-prec-inv prec v V-ƛ ⟩ of λ where
        ⟨ V-ƛ , ⊑-lam gc⊑gc′ A⊑A′ N⊑N′ , c⊑c′ , refl , refl ⟩ →
          case ⟨ i , c⊑c′ ⟩ of λ where
          ⟨ ir-fun {c = c} {d} {c̅} {d̅} 𝓋 , ⊑-fun {d̅′ = d̅′} {c̅′ = c̅′} d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ ⟩ → ?
        --     let ∣c̅∣≼∣c̅′∣ : ∥ c̅ ∥ₗ 𝓋 ≼ ∥ c̅′ ∥ₗ 𝓋′
        --         ∣c̅∣≼∣c̅′∣ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′
        --         ∣c̅∣≼ℓ₂ : ∥ c̅ ∥ₗ 𝓋 ≼ ℓ₂
        --         ∣c̅∣≼ℓ₂ = subst (λ □ → _ ≼ □) (static-security _ 𝓋′) ∣c̅∣≼∣c̅′∣ in
        --     let pc-prec : (stamp!ₑ PC vc (∥ c̅ ∥ₗ 𝓋) ⟪ d̅ ⟫) ⊑ (stampₑ PC′ vc′ ℓ₂ ⟪ d̅′ ⟫) ⇐ _ ⊑ g₁
        --         pc-prec = ⊑-cast (stamp!ₑ-left-prec vc vc′ PC⊑PC′ ∣c̅∣≼ℓ₂) d̅⊑d̅′ in
        --     let ⟨ PC₁ , vc₁ , ↠PC₁ , pc-prec′ ⟩ = sim-mult pc-prec ↠PC″ vc″ in
        --     let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast W⊑M′ w v′ c⊑c′ ↠W′ w′ in
        --     let ♣ = trans-mult (plug-cong (app!□ _ _ _) L↠V)
        --             (trans-mult (plug-cong (app! _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _) M↠W)
        --             (_ ∣ _ ∣ _ —→⟨ app!-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
        --     ⟨ _ , ♣ ,
        --       ⊑-prot!l (⊑-cast (substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑W′ w₁ w′)) d⊑d′)
        --         pc-prec′ (stamp!-cast-security vc ⊢PC ↠PC₁ vc₁)
        --         (stamp-cast-security vc′ ⊢PC′ ↠PC″ vc″)
        --         eq eq′ ∣c̅∣≼ℓ₂ ⟩
      ⟨ V-● , ●⊑ ⟩ → contradiction ●⊑ (●⋤ _)
sim-app!-cast vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ =
  case sim-app!-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋′ ↠PC″ vc″ ↠W′ w′ of λ where
  ⟨ N , M↠N , N⊑N′ ⟩ →
    ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
