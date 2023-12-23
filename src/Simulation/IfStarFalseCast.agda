module Simulation.IfStarFalseCast where

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

open import Common.Utils
open import Memory.HeapContext
open import LabelExpr.Security
open import LabelExpr.Stamping
open import LabelExpr.GG
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision
open import Simulation.CatchUp
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

open import Simulation.SimCast


sim-if⋆-false-cast : ∀ {Σ Σ′ gc gc′} {M M′ N′ μ μ′ PC PC′} {A A′ T′} {ℓ}
                        {c̅ : CExpr l ℓ ⇒ ⋆}
    → (vc  : LVal PC)
    → (vc′ : LVal PC′)
    → let ℓv  = ∥ PC  ∥ vc  in
       let ℓv′ = ∥ PC′ ∥ vc′ in
       [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
         M ⊑ if⋆ ($ false ⟨ cast (id Bool) c̅ ⟩) T′ M′ N′ ⇐ A ⊑ A′
    → Σ ⊑ₘ Σ′
    → Σ ; Σ′ ⊢ μ ⊑ μ′
    → PC ⊑ PC′ ⇐ gc ⊑ gc′
    → SizeEq μ μ′
    → (𝓋′  : CVal c̅)
      --------------------------------------------------------------------------
    → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
              (let ℓ′ = ∥ c̅ ∥ₗ 𝓋′ in
               [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
                     N ⊑ prot (stamp!ₑ PC′ vc′ ℓ′) (stamp!ₑ-LVal vc′) ℓ′ N′ (T′ of ⋆)
                  ⇐ A ⊑ A′)
sim-if⋆-false-cast {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-if⋆ {L = L} {L′} {M} {M′} {N} {N′} L⊑L′ M⊑M′ N⊑N′)
    Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq 𝓋′ =
  case catchup {μ = μ} {PC} (V-cast V-const (ir-base 𝓋′ (λ ()))) L⊑L′ of λ where
  ⟨ V , v , L↠V , prec ⟩ →
    case ⟨ v , prec ⟩ of λ where
    ⟨ V-raw V-const , ⊑-castr () (⊑-base _) ⟩
    ⟨ V-cast v i , prec ⟩ →
      case ⟨ v , cast-prec-inv prec v V-const ⟩ of λ where
      ⟨ V-const , ⊑-const , c⊑c′ , refl , refl ⟩ →
        case ⟨ i , c⊑c′ ⟩ of λ where
        ⟨ ir-base (inj 𝓋) x , ⊑-base c̅⊑c̅′ ⟩ →
          ⟨ _ ,
            trans-mult (plug-cong (if⋆□ _ _ _) L↠V)
                       (_ ∣ _ ∣ _ —→⟨ if⋆-false-cast vc (inj 𝓋) ⟩ _ ∣ _ ∣ _ ∎) ,
            (let ∣c̅∣≼∣c̅′∣ = security-prec _ _ (inj 𝓋) 𝓋′ c̅⊑c̅′ in
             ⊑-prot! N⊑N′ (stamp!ₑ-prec vc vc′ PC⊑PC′ ∣c̅∣≼∣c̅′∣)
                   (≡→≼ (stamp!ₑ-security vc)) (≡→≼ (stamp!ₑ-security vc′)) ∣c̅∣≼∣c̅′∣) ⟩
sim-if⋆-false-cast vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq 𝓋′ =
  case sim-if⋆-false-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq 𝓋′ of λ where
  ⟨ N , M↠N , N⊑N′ ⟩ →
    ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
