module Simulation.IfFalseCast where

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


sim-if-false-cast : ∀ {Σ Σ′ gc gc′} {M M′ N′ μ μ′ PC PC′} {A A′ B′}
    → (vc  : LVal PC)
    → (vc′ : LVal PC′)
    → let ℓv  = ∥ PC  ∥ vc  in
       let ℓv′ = ∥ PC′ ∥ vc′ in
       [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
         M ⊑ if ($ false ⟨ cast (id Bool) (id (l low) ⨾ ↑) ⟩) B′ high M′ N′ ⇐ A ⊑ A′
    → Σ ⊑ₘ Σ′
    → Σ ; Σ′ ⊢ μ ⊑ μ′
    → PC ⊑ PC′ ⇐ gc ⊑ gc′
    → SizeEq μ μ′
      --------------------------------------------------------------------------
    → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
              [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
                     N ⊑ prot (stampₑ PC′ vc′ high) (stampₑ-LVal vc′) high N′ B′
                  ⇐ A ⊑ A′
sim-if-false-cast {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-if {ℓc = ℓc} {L = L} {L′} {M} {M′} {N} {N′} {ℓ = ℓ} L⊑L′ M⊑M′ N⊑N′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq =
  case catchup {μ = μ} {PC} (V-cast V-const (ir-base (up id) (λ ()))) L⊑L′ of λ where
  ⟨ V , v , L↠V , prec ⟩ →
    case ⟨ v , prec ⟩ of λ where
    ⟨ V-raw V-const , ⊑-castr () (⊑-base _) ⟩
    ⟨ V-cast v i , prec ⟩ →
      case ⟨ v , cast-prec-inv prec v V-const ⟩ of λ where
      ⟨ V-const , ⊑-const , c⊑c′ , refl , refl ⟩ →
        case ⟨ i , c⊑c′ ⟩ of λ where
        ⟨ ir-base (up id) x , ⊑-base c̅⊑c̅′ ⟩ →
          ⟨ _ ,
            trans-mult (plug-cong (if□ _ _ _ _) L↠V)
                       (_ ∣ _ ∣ _ —→⟨ if-false-cast vc ⟩ _ ∣ _ ∣ _ ∎) ,
            ⊑-prot N⊑N′ (stampₑ-prec vc vc′ PC⊑PC′)
                   (≡→≼ (stampₑ-security vc)) (≡→≼ (stampₑ-security vc′)) eq eq′ ⟩
sim-if-false-cast {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-if!l {ℓc = ℓc} {L = L} {L′} {M} {M′} {N} {N′} {ℓ = ℓ} L⊑L′ M⊑M′ N⊑N′ eq′)
    Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq =
  case catchup {μ = μ} {PC} (V-cast V-const (ir-base (up id) (λ ()))) L⊑L′ of λ where
  ⟨ V , v , L↠V , prec ⟩ →
    case ⟨ v , prec ⟩ of λ where
    ⟨ V-raw V-const , ⊑-castr () (⊑-base _) ⟩
    ⟨ V-cast v i , prec ⟩ →
      case ⟨ v , cast-prec-inv prec v V-const ⟩ of λ where
      ⟨ V-const , ⊑-const , c⊑c′ , refl , refl ⟩ →
        case ⟨ i , c⊑c′ ⟩ of λ where
        ⟨ ir-base (inj 𝓋) x , ⊑-base c̅⊑c̅′ ⟩ →
          ⟨ _ ,
            trans-mult (plug-cong (if!□ _ _ _) L↠V)
                       (_ ∣ _ ∣ _ —→⟨ if!-false-cast vc (inj 𝓋) ⟩ _ ∣ _ ∣ _ ∎) ,
            ⊑-prot!l N⊑N′ (stamp!ₑ-left-prec vc vc′ PC⊑PC′ (_ ≼high))
                   (≡→≼ (stamp!ₑ-security vc)) (≡→≼ (stampₑ-security vc′)) eq′ (_ ≼high) ⟩
sim-if-false-cast vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq =
  case sim-if-false-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq of λ where
  ⟨ N , M↠N , N⊑N′ ⟩ →
    ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
