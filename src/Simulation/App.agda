module Simulation.App where

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


sim-app : ∀ {Σ Σ′ gc gc′} {M N′ V′ μ μ′ PC PC′} {A A′ B′ C′} {ℓ}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ app (ƛ N′) V′ B′ C′ ℓ ⇐ A ⊑ A′
  → Σ ⊑ₘ Σ′
  → Σ ; Σ′ ⊢ μ ⊑ μ′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ μ′
  → Value V′
    --------------------------------------------------------------------------
  → ∃[ N ] (M ∣ μ ∣ PC —↠ N ∣ μ) ×
            ([] ; [] ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢
              N ⊑ prot (stampₑ PC′ vc′ ℓ) (stampₑ-LVal vc′) ℓ (N′ [ V′ ]) C′
              ⇐ A ⊑ A′)
sim-app {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-app {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
  with catchup {μ = μ} {PC} (V-raw V-ƛ) L⊑L′
... | ⟨ V , V-raw V-ƛ , L↠V , ⊑-lam g⊑g′ A⊑A′ N⊑N′ ⟩ =
  case catchup {μ = μ} {PC} v′ M⊑M′ of λ where
  ⟨ W , w , M↠W , W⊑M′ ⟩ →
    let ♣ = trans-mult (plug-cong (app□ M _ _ _) L↠V)
              (trans-mult (plug-cong (app _ □ (V-raw V-ƛ) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ β w vc ⟩ _ ∣ _ ∣ _ ∎)) in
    let N[W]⊑N′[M′] = substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W⊑M′ w v′) in
    ⟨ _ , ♣ ,
      ⊑-prot N[W]⊑N′[M′] (stampₑ-prec vc vc′ PC⊑PC′) (≡→≼ (stampₑ-security vc)) (≡→≼ (stampₑ-security vc′)) eq eq′ ⟩
... | ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ ⟩ , V-cast V-ƛ (ir-fun 𝓋) ,
        L↠V , ⊑-castl (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun {gc₁ = gc₁} d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) ⟩
  with catchup {μ = μ} {PC} v′ M⊑M′
...   | ⟨ W , w , M↠W , W⊑M′ ⟩
  with catchup {μ = μ} {PC} v′ (⊑-castl W⊑M′ c⊑A′)
...   | ⟨ W₁ , w₁ , W⟨c⟩↠W₁ , W₁⊑M′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ , PC₁⊑stampPC′ ⟩ = catchupₑ (stampₑ-LVal vc′) prec in
  let ♣ = trans-mult (plug-cong (app□ M _ _ _) L↠V)
              (trans-mult (plug-cong (app _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ app-cast w vc 𝓋 ↠PC₁ vc₁ (cast-reduction-inv w W⟨c⟩↠W₁ refl) w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  let N[W₁]⊑N′[M′] = substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑M′ w₁ v′) in
  ⟨ _ , ♣ ,
    ⊑-prot (⊑-castl N[W₁]⊑N′[M′] d⊑B′) PC₁⊑stampPC′ (stamp-cast-security vc ⊢PC ↠PC₁ vc₁) (≡→≼ (stampₑ-security vc′)) eq eq′ ⟩
  where
  ⊢W = proj₁ (cc-prec-inv ⊑*-∅ Σ⊑Σ′ W⊑M′)
  ⊢PC = proj₁ (prec→⊢ PC⊑PC′)
  prec : (stampₑ PC vc ℓ ⟪ d̅ ⟫) ⊑ stampₑ PC′ vc′ ℓ
                   ⇐ gc₁ ⊑ (gc′ ⋎̃ (l ℓ))
  prec = ⊑-castl (stampₑ-prec vc vc′ PC⊑PC′) d̅⊑gc′
sim-app {Σ} {Σ′} {gc} {gc′} {μ = μ} {PC = PC} {PC′} vc vc′
    (⊑-app⋆l {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq′)
    Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
  with catchup {μ = μ} {PC} (V-raw V-ƛ) L⊑L′
... | ⟨ V , V-raw V-ƛ , L↠V , () ⟩
... | ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ ⟩ , V-cast V-ƛ (ir-fun 𝓋) ,
        L↠V , ⊑-castl (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun {gc₁ = gc₁} {.⋆} d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) ⟩
  with catchup {μ = μ} {PC} v′ M⊑M′
...   | ⟨ W , w , M↠W , W⊑M′ ⟩
  with catchup {μ = μ} {PC} v′ (⊑-castl W⊑M′ c⊑A′)
...   | ⟨ W₁ , w₁ , W⟨c⟩↠W₁ , W₁⊑M′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ , PC₁⊑stampPC′ ⟩ = catchupₑ (stampₑ-LVal vc′) prec in
  let ♣ = trans-mult (plug-cong (app⋆□ M _ _) L↠V)
              (trans-mult (plug-cong (app⋆ _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ app⋆-cast w vc 𝓋 ↠PC₁ vc₁ (cast-reduction-inv w W⟨c⟩↠W₁ refl) w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ _ , ♣ ,
    ⊑-prot!l (⊑-castl (substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑M′ w₁ v′)) d⊑B′)
             PC₁⊑stampPC′
             (stamp!-cast-security vc ⊢PC ↠PC₁ vc₁) (≡→≼ (stampₑ-security vc′)) eq′ (≡→≼ ∥c̅∥≡ℓ) ⟩
  where
  ∥PC∥⋎∥c̅∥≡∥stamp∥ = stampₑ-security {ℓ = ∥ c̅ ∥ₗ 𝓋} vc
  ∥c̅∥≡ℓ = security-prec-left _ 𝓋 c̅⊑g′
  ⊢PC = proj₁ (prec→⊢ PC⊑PC′)
  ⊢W = proj₁ (cc-prec-inv ⊑*-∅ Σ⊑Σ′ W⊑M′)
  prec : (stamp!ₑ PC vc (∥ c̅ ∥ₗ 𝓋) ⟪ d̅ ⟫) ⊑ stampₑ PC′ vc′ ℓ
                   ⇐ gc₁ ⊑ (gc′ ⋎̃ (l ℓ))
  prec rewrite ∥c̅∥≡ℓ = ⊑-castl (stamp!ₑ-left-prec vc vc′ PC⊑PC′ ≼-refl) d̅⊑gc′
sim-app vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
  with sim-app vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′
... | ⟨ N , M↠N , N⊑N′ ⟩ =
  ⟨ N ⟨ c ⟩ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ ⟩
