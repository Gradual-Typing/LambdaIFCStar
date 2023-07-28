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


sim : ∀ {Γ Γ′ Σ₁ Σ₁′ gc gc′} {M M′ N′ μ₁ μ₁′ μ₂′ PC PC′} {A A′}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     Γ ; Γ′ ∣ Σ₁ ; Σ₁′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
  → Γ ⊑* Γ′
  → Σ₁ ⊑ₘ Σ₁′
  → Σ₁ ; Σ₁′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → M′ ∣ μ₁′ ∣ PC′ —→ N′ ∣ μ₂′
    ------------------------------------------------------
  → ∃[ Σ₂ ] ∃[ Σ₂′ ] ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       (Γ ; Γ′ ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′) ×
       (Σ₂ ; Σ₂′ ⊢ μ₂ ⊑ μ₂′)
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ξ M′→N′) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ ξ-blame = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot-val v) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ prot-blame = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot!-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot!-val v) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ prot!-blame = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (cast x x₁) = {!!}
sim vc vc′ (⊑-app L⊑L′ M⊑M′ eq eq′) Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β vM′ vc′†) =
  {!!}
sim {Γ} {Γ′} {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-app!l {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq eq′)
    Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β vM′ vc′†)
  rewrite uniq-LVal vc′† vc′
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
  ⟨ Σ , Σ′ , _ , μ , ♣ , ⊑-prot!l {!!} PC₁⊑stampPC′ {!!} {!!} {!!} {!!} {!!} , μ⊑μ′ ⟩
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

sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app-cast v vc′† 𝓋 x vc″ x₁ x₂) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app-blame-pc v vc′† 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app-blame v vc′† 𝓋 x vc″ x₁) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app!-cast v vc′† 𝓋 x x₁ vc″ x₂ x₃) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app!-blame-pc v vc′† 𝓋 x x₁) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app!-blame v vc′† 𝓋 x x₁ vc″ x₂) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-if-true vc′†) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-if-false vc′†) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if-true-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if-false-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if!-true-cast vc′† 𝓋 x x₁ vc″) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if!-false-cast vc′† 𝓋 x x₁ vc″) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-let x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ref v x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ref? v x x₁ x₂) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ref?-blame-pc v x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (deref x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (deref-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (deref!-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-assign v) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign-cast v 𝓋 x w) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign-blame v 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-assign? v vc′† x x₁ x₂) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign?-blame-pc v vc′† x x₁) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign?-cast v vc′† 𝓋 x x₁ x₂ x₃ w) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign?-cast-blame-pc v vc′† 𝓋 x x₁) = {!!}
sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign?-cast-blame v vc′† 𝓋 x x₁ x₂ x₃) = {!!}
sim vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ M′→N′
  with sim vc vc′ M⊑M′ Γ⊑Γ′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ M′→N′
... | ⟨ Σ₂ , Σ₂′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ ⟩ =
  ⟨ Σ₂ , Σ₂′ , N ⟨ c ⟩ , μ₂ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ₂⊑μ₂′ ⟩
