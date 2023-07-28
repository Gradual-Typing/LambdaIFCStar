module CC2.Sim where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
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
open import LabelExpr.CatchUp renaming (catchup to catchupₑ)
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.CatchUp


sim : ∀ {Γ Γ′ Σ₁ Σ₁′ gc gc′ ℓv ℓv′} {M M′ N′ μ₁ μ₁′ μ₂′ PC PC′} {A A′}
  → Γ ; Γ′ ∣ Σ₁ ; Σ₁′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
  → Γ ⊑* Γ′
  → Σ₁ ⊑ₘ Σ₁′
  → Σ₁ ; Σ₁′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → LVal PC
  → M′ ∣ μ₁′ ∣ PC′ —→ N′ ∣ μ₂′
    ------------------------------------------------------
  → ∃[ Σ₂ ] ∃[ Σ₂′ ] ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       (Γ ; Γ′ ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′) ×
       (Σ₂ ; Σ₂′ ⊢ μ₂ ⊑ μ₂′)
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (ξ M′→N′) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc ξ-blame = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (prot-ctx M′→N′) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (prot-val v) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc prot-blame = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (prot!-ctx M′→N′) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (prot!-val v) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc prot!-blame = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (cast x x₁) = {!!}
sim (⊑-app L⊑L′ M⊑M′ eq eq′) Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (β vM′ vc′) =
  {!!}
sim {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′}
    (⊑-app!l {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq eq′)
    Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (β vM′ vc′)
  with catchup {μ = μ} {PC} (V-raw V-ƛ) L⊑L′
... | ⟨ V , V-raw V-ƛ , L↠V , () ⟩
... | ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ ⟩ , V-cast V-ƛ (ir-fun 𝓋) ,
        L↠V , ⊑-castl (⊑-lam x y z) (⊑-fun {gc₁ = gc₁} {.⋆} d̅⊑gc′ _ _ c̅⊑g′) ⟩
  with catchup {μ = μ} {PC} vM′ M⊑M′
...   | ⟨ W , w , M↠W , W⊑M′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ , PC₁⊑stampPC′ ⟩ = catchupₑ (stampₑ-LVal vc′) prec in
  let ♣ = trans-mult (plug-cong (app!□ M _ _) L↠V)
          (trans-mult (plug-cong (app! _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _) M↠W)
          (_ ∣ _ ∣ _ —→⟨ app!-cast w vc 𝓋 ⊢PC ↠PC₁ vc₁ {!!} {!!} ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ Σ , Σ′ , _ , μ , ♣ , ⊑-prot!l {!!} {!!} {!!} {!!} {!!} {!!} {!!} , μ⊑μ′ ⟩
  where
  ⊢PC = proj₁ (prec→⊢ PC⊑PC′)
  gc⊑ℓc : gc ⊑ₗ l ℓc
  gc⊑ℓc = prec→⊑ PC⊑PC′
  gc⋎ℓ⊑ℓc⋎ℓ : (gc ⋎̃ l ℓ) ⊑ₗ (l (ℓc ⋎ ℓ))
  gc⋎ℓ⊑ℓc⋎ℓ = consis-join-⊑ₗ gc⊑ℓc l⊑l
  prec : (stampₑ PC vc (∥ c̅ ∥ₗ 𝓋) ⟪ coerce gc ⋎̃ l (∥ c̅ ∥ₗ 𝓋) ⇒⋆ ⟫ ⟪ d̅ ⟫) ⊑ stampₑ PC′ vc′ ℓ
           ⇐ gc₁ ⊑ (gc′ ⋎̃ (l ℓ))
  prec rewrite security-prec-left _ 𝓋 c̅⊑g′ =
    ⊑-castl (⊑-castl (stampₑ-pres-prec vc vc′ PC⊑PC′) (coerce⇒⋆-prec gc⋎ℓ⊑ℓc⋎ℓ)) d̅⊑gc′

sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (app-cast v vc′ 𝓋 x vc″ x₁ x₂) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (app-blame-pc v vc′ 𝓋 x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (app-blame v vc′ 𝓋 x vc″ x₁) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (app!-cast v vc′ 𝓋 x x₁ vc″ x₂ x₃) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (app!-blame-pc v vc′ 𝓋 x x₁) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (app!-blame v vc′ 𝓋 x x₁ vc″ x₂) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (β-if-true vc′) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (β-if-false vc′) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (if-true-cast vc′) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (if-false-cast vc′) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (if!-true-cast vc′ 𝓋 x x₁ vc″) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (if!-false-cast vc′ 𝓋 x x₁ vc″) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (β-let x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (ref v x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (ref? v x x₁ x₂) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (ref?-blame-pc v x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (deref x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (deref-cast 𝓋 x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (deref!-cast 𝓋 x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (β-assign v) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (assign-cast v 𝓋 x w) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (assign-blame v 𝓋 x) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (β-assign? v vc′ x x₁ x₂) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (assign?-blame-pc v vc′ x x₁) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (assign?-cast v vc′ 𝓋 x x₁ x₂ x₃ w) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (assign?-cast-blame-pc v vc′ 𝓋 x x₁) = {!!}
sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc (assign?-cast-blame v vc′ 𝓋 x x₁ x₂ x₃) = {!!}
sim (⊑-castl {c = c} M⊑M′ c⊑A′) Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc M′→N′
  with sim M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ vc M′→N′
... | ⟨ Σ₂ , Σ₂′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ ⟩ =
  ⟨ Σ₂ , Σ₂′ , N ⟨ c ⟩ , μ₂ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ₂⊑μ₂′ ⟩
