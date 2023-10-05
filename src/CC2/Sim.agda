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
open import CoercionExpr.SyntacComp
open import LabelExpr.CatchUp renaming (catchup to catchupₑ)
open import LabelExpr.Security
open import LabelExpr.Stamping
open import LabelExpr.NSU
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapTyping using (⊇-fresh)
open import CC2.HeapPrecision
open import CC2.CatchUp
open import CC2.SimCast
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

{- One lemma for each reduction rule (on the more precise side) -}
open import CC2.Simulation.App
open import CC2.Simulation.Assign
open import CC2.Simulation.AssignCast
open import CC2.Simulation.Assign?Cast
open import CC2.Simulation.Deref
open import CC2.Simulation.Deref!Cast
open import CC2.Simulation.DerefCast


sim : ∀ {Σ₁ Σ₁′ gc gc′} {M M′ N′ μ₁ μ₁′ μ₂′ PC PC′} {A A′}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ₁ ; Σ₁′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
  → Σ₁ ⊑ₘ Σ₁′
  → Σ₁ ; Σ₁′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ₁ μ₁′
  → M′ ∣ μ₁′ ∣ PC′ —→ N′ ∣ μ₂′
    ------------------------------------------------------
  → ∃[ Σ₂ ] ∃[ Σ₂′ ]
       (Σ₂ ⊇ Σ₁) × (Σ₂′ ⊇ Σ₁′) ×
     ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′) ×
       (Σ₂ ; Σ₂′ ⊢ μ₂ ⊑ μ₂′) ×
       (SizeEq μ₂ μ₂′)

-- reasoning about evaluation contexts
sim-ξ : ∀ {Σ₁ Σ₁′ gc gc′} {M M′ N′ μ₁ μ₁′ μ₂′ PC PC′} {A A′} {F : Frame}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ₁ ; Σ₁′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ plug M′ F ⇐ A ⊑ A′
  → Σ₁ ⊑ₘ Σ₁′
  → Σ₁ ; Σ₁′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ₁ μ₁′
  → M′ ∣ μ₁′ ∣ PC′ —→ N′ ∣ μ₂′
    ------------------------------------------------------
  → ∃[ Σ₂ ] ∃[ Σ₂′ ]
       (Σ₂ ⊇ Σ₁) × (Σ₂′ ⊇ Σ₁′) ×
     ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ plug N′ F ⇐ A ⊑ A′) ×
       (Σ₂ ; Σ₂′ ⊢ μ₂ ⊑ μ₂′) ×
       (SizeEq μ₂ μ₂′)
sim-ξ {F = app□ M A B ℓ}
      vc vc′ (⊑-app L⊑L′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq L′→N′ =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , L↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
           sim vc vc′ L⊑L′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq L′→N′ in
  ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ , plug-cong (app□ _ _ _ _) L↠N ,
    ⊑-app N⊑N′ (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) eq eq′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ {F = app□ M A B ℓ}
      vc vc′ (⊑-app!l L⊑L′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq L′→N′ =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , L↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
           sim vc vc′ L⊑L′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq L′→N′ in
  ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ , plug-cong (app!□ _ _ _) L↠N ,
    ⊑-app!l N⊑N′ (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) eq eq′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ {μ₁ = μ} {PC = PC} {PC′} {F = app V′ □ v′ A B ℓ}
      vc vc′ (⊑-app L⊑V′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ =
  case catchup {μ = μ} {PC} v′ L⊑V′ of λ where
  ⟨ V , v , L↠V , V⊑V′ ⟩ →
    let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
             sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ in
    ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ ,
      trans-mult (plug-cong (app□ _ _ _ _) L↠V)
                 (plug-cong (app V □ v _ _ _) M↠N) ,
      ⊑-app (prec-relax-Σ V⊑V′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) N⊑N′ eq eq′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ {μ₁ = μ} {PC = PC} {F = app V′ □ v′ A B ℓ}
      vc vc′ (⊑-app!l L⊑V′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ =
  case catchup {μ = μ} {PC} v′ L⊑V′ of λ where
  ⟨ V , v , L↠V , V⊑V′ ⟩ →
    let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
             sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ in
    ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ ,
      trans-mult (plug-cong (app!□ _ _ _) L↠V)
                 (plug-cong (app! V □ v _ _) M↠N) ,
      ⊑-app!l (prec-relax-Σ V⊑V′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) N⊑N′ eq eq′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ {F = app!□ M′ A B} vc vc′ (⊑-app! L⊑L′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq L′→N′ =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , L↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
           sim vc vc′ L⊑L′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq L′→N′ in
  ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ , plug-cong (app!□ _ _ _) L↠N ,
    ⊑-app! N⊑N′ (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) eq eq′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ {μ₁ = μ} {PC = PC} {F = app! V′ □ v′ A B}
      vc vc′ (⊑-app! L⊑V′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ =
  case catchup {μ = μ} {PC} v′ L⊑V′ of λ where
  ⟨ V , v , L↠V , V⊑V′ ⟩ →
    let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
             sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ in
    ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ ,
      trans-mult (plug-cong (app!□ _ _ _) L↠V)
                 (plug-cong (app! V □ v _ _) M↠N) ,
      ⊑-app! (prec-relax-Σ V⊑V′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) N⊑N′ eq eq′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ {F = ref⟦ ℓ ⟧□} vc vc′ (⊑-ref M⊑M′ x) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = ref⟦ ℓ ⟧□} vc vc′ (⊑-ref?l M⊑M′ x) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = ref?⟦ ℓ ⟧□ p} vc vc′ (⊑-ref? M⊑M′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = !□ x x₁} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = !!□ x} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = assign□ M x ℓ̂ ℓ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = assign V □ x x₁ ℓ̂ ℓ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = assign?□ M x ĝ x₁} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = assign? V □ x x₁ ĝ x₂} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = let□ x x₁} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = if□ x x₁ M N} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = if!□ x M N} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ = {!!}
sim-ξ {F = □⟨ c′ ⟩} vc vc′ (⊑-cast M⊑M′ c⊑c′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
           sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ in
  ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ , plug-cong □⟨ _ ⟩ M↠N ,
    ⊑-cast N⊑N′ c⊑c′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ {F = □⟨ c′ ⟩} vc vc′ (⊑-castr M⊑M′ A⊑c′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
           sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ in
  ⟨ _ , _ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , _ , M↠N , ⊑-castr N⊑N′ A⊑c′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim-ξ vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ =
  case sim-ξ vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′ of λ where
  ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ →
    ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N ⟨ c ⟩ , μ₂ ,
      plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ₂⊑μ₂′ , size-eq′ ⟩


{- ξ -}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ξ M′→N′) =
  sim-ξ vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′

sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq ξ-blame =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩

{- prot-ctx -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-prot {vc = vc₁} {vc₁′} M⊑M′ PC₁⊑PC₁′ ℓv₁⋎ℓ≼ℓv₂ ℓv₁′⋎ℓ≼ℓv₂′ eq eq′)
  Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot-ctx M′→N′) =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
        sim vc₁ vc₁′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC₁⊑PC₁′ size-eq M′→N′ in
  ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , μ₂ , prot-ctx-mult vc₁ M↠N ,
    ⊑-prot N⊑N′ PC₁⊑PC₁′ ℓv₁⋎ℓ≼ℓv₂ ℓv₁′⋎ℓ≼ℓv₂′ eq eq′ , μ₂⊑μ₂′ , size-eq′ ⟩
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-prot!l {vc = vc₁} {vc₁′} M⊑M′ PC₁⊑PC₁′ ℓv₁⋎ℓ≼ℓv₂ ℓv₁′⋎ℓ≼ℓv₂′ eq eq′ ℓ≼ℓ′)
  Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot-ctx M′→N′) =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
        sim vc₁ vc₁′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC₁⊑PC₁′ size-eq M′→N′ in
  ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , μ₂ , prot!-ctx-mult vc₁ M↠N ,
    ⊑-prot!l N⊑N′ PC₁⊑PC₁′ ℓv₁⋎ℓ≼ℓv₂ ℓv₁′⋎ℓ≼ℓv₂′ eq eq′ ℓ≼ℓ′ , μ₂⊑μ₂′ , size-eq′ ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot-val v) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq prot-blame =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩

{- prot!-ctx -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-prot! {vc = vc₁} {vc₁′} M⊑M′ PC₁⊑PC₁′ ℓv₁⋎ℓ≼ℓv₂ ℓv₁′⋎ℓ≼ℓv₂′ eq eq′ ℓ≼ℓ′)
  Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot!-ctx M′→N′) =
  let ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
        sim vc₁ vc₁′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC₁⊑PC₁′ size-eq M′→N′ in
  ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , _ , μ₂ , prot!-ctx-mult vc₁ M↠N ,
    ⊑-prot! N⊑N′ PC₁⊑PC₁′ ℓv₁⋎ℓ≼ℓv₂ ℓv₁′⋎ℓ≼ℓv₂′ eq eq′ ℓ≼ℓ′ , μ₂⊑μ₂′ , size-eq′ ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot!-val v) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq prot!-blame =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (cast x x₁) = {!!}

{- β -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β vM′ vc′†)
  rewrite uniq-LVal vc′† vc′ =
  let ⟨ N , ♣ , prec ⟩ = sim-app vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq vM′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , N , μ , ♣ , prec , μ⊑μ′ , size-eq ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-cast v vc′† 𝓋 x vc″ x₁ x₂) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-blame-pc v vc′† 𝓋 x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-blame v vc′† 𝓋 x vc″ x₁) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-cast v vc′† 𝓋 _ _ _ _) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-blame-pc v vc′† 𝓋 _) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-blame v vc′† 𝓋 _ _ _) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-if-true vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-if-false vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if-true-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if-false-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if!-true-cast vc′† 𝓋) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if!-false-cast vc′† 𝓋) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-let x) = {!!}

{- ref -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-ref {T = T} {T′} {ℓ} M⊑V′ ℓc≼ℓ) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref {n = n} v′ fresh′)
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ V , v , M↠V , V⊑V′ ⟩ =
  let fresh = size-eq-fresh size-eq fresh′ in
  let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , cons-Σ (a⟦ ℓ ⟧ n) T′ Σ′ ,
    ⊇-fresh (a⟦ ℓ ⟧ n) T ⊢μ fresh , ⊇-fresh (a⟦ ℓ ⟧ n) T′ ⊢μ′ fresh′ ,
    _ , cons-μ (a⟦ ℓ ⟧ n) _ v μ ,
    trans-mult (plug-cong (ref⟦ _ ⟧□) M↠V)
               (_ ∣ _ ∣ _ —→⟨ ref v fresh ⟩ _ ∣ _ ∣ _ ∎) ,
    ⊑-addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ′) ,
    ⊑μ-new Σ⊑Σ′ μ⊑μ′ (value-⊑-pc V⊑V′ v v′) v v′ fresh fresh′ ,
    size-eq-cons {v = v} {v′} {n} {ℓ} size-eq ⟩
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
  (⊑-ref?l {T = T} {T′} {ℓ} M⊑V′ ℓc≼ℓ) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref {n = n} v′ fresh′)
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ V , v , M↠V , V⊑V′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-ref-left PC⊑PC′ vc vc′ ℓc≼ℓ in
  let fresh = size-eq-fresh size-eq fresh′ in
  let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , cons-Σ (a⟦ ℓ ⟧ n) T′ Σ′ ,
    ⊇-fresh (a⟦ ℓ ⟧ n) T ⊢μ fresh , ⊇-fresh (a⟦ ℓ ⟧ n) T′ ⊢μ′ fresh′ ,
    _ , cons-μ (a⟦ ℓ ⟧ n) _ v μ ,
    trans-mult (plug-cong (ref?⟦ _ ⟧□ _) M↠V)
               (_ ∣ _ ∣ _ —→⟨ ref? v fresh ↠PC₁ vc₁ ⟩ _ ∣ _ ∣ _ ∎) ,
    ⊑-addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ′) ,
    ⊑μ-new Σ⊑Σ′ μ⊑μ′ (value-⊑-pc V⊑V′ v v′) v v′ fresh fresh′ ,
    size-eq-cons {v = v} {v′} {n} {ℓ} size-eq ⟩

{- ref? -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-ref? {T = T} {T′} {ℓ} M⊑V′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref? {n = n} v′ fresh′ ↠PC′₁ vc′₁)
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ V , v , M↠V , V⊑V′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-ref PC⊑PC′ vc vc′ ↠PC′₁ vc′₁ in
  let fresh = size-eq-fresh size-eq fresh′ in
  let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , cons-Σ (a⟦ ℓ ⟧ n) T′ Σ′ ,
    ⊇-fresh (a⟦ ℓ ⟧ n) T ⊢μ fresh , ⊇-fresh (a⟦ ℓ ⟧ n) T′ ⊢μ′ fresh′ ,
    _ , cons-μ (a⟦ ℓ ⟧ n) _ v μ ,
    trans-mult (plug-cong (ref?⟦ _ ⟧□ _) M↠V)
               (_ ∣ _ ∣ _ —→⟨ ref? v fresh ↠PC₁ vc₁ ⟩ _ ∣ _ ∣ _ ∎) ,
    ⊑-addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ′) ,
    ⊑μ-new Σ⊑Σ′ μ⊑μ′ (value-⊑-pc V⊑V′ v v′) v v′ fresh fresh′ ,
    size-eq-cons {v = v} {v′} {n} {ℓ} size-eq ⟩

sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref?-blame-pc v x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩

{- deref -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref {v = v′} μ′a≡V′) =
  let ⟨ N , ♣ , prec ⟩ = sim-deref vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ μ′a≡V′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , N , μ , ♣ , prec , μ⊑μ′ , size-eq ⟩

{- deref-cast -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref-cast {v = v′} 𝓋 μ′a≡V′) =
  let ⟨ N , ♣ , prec ⟩ = sim-deref-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋 μ′a≡V′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , N , μ , ♣ , prec , μ⊑μ′ , size-eq ⟩

{- deref!-cast -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref!-cast {v = v′} 𝓋 μ′a≡V′) =
  let ⟨ N , ♣ , prec ⟩ = sim-deref!-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ 𝓋 μ′a≡V′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , N , μ , ♣ , prec , μ⊑μ′ , size-eq ⟩

{- assign -}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-assign v) =
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , sim-assign vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v ⟩

{- assign-cast -}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign-cast v′ 𝓋′ ↠W′ w′) =
    ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , sim-assign-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq  v′ 𝓋′ ↠W′ w′ ⟩
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign-blame v 𝓋 x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩

{- assign?-cast -}
sim {Σ} {Σ′} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast v′ vc′† 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′)
    rewrite uniq-LVal vc′† vc′ =
    ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , sim-assign?-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq  v′ 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′ ⟩

sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast-blame-pc v vc′† 𝓋 x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast-blame v vc′† 𝓋 x x₁ x₂) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , ⊇-refl Σ , ⊇-refl Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′
  with sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′
... | ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
  ⟨ Σ₂ , Σ₂′ , Σ₂⊇Σ₁ , Σ₂′⊇Σ₁′ , N ⟨ c ⟩ , μ₂ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ₂⊑μ₂′ , size-eq′ ⟩
