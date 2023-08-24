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
open import CC2.HeapPrecision
open import CC2.CatchUp
open import CC2.SimCast
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

open import CC2.Simulation.App
open import CC2.Simulation.Assign?Cast
open import CC2.Simulation.Deref


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
  → ∃[ Σ₂ ] ∃[ Σ₂′ ] ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′) ×
       (Σ₂ ; Σ₂′ ⊢ μ₂ ⊑ μ₂′) ×
       (SizeEq μ₂ μ₂′)
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ξ M′→N′) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq ξ-blame =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot-val v) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq prot-blame =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot!-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot!-val v) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq prot!-blame =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (cast x x₁) = {!!}

{- β -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β vM′ vc′†)
  rewrite uniq-LVal vc′† vc′ =
  let ⟨ N , ♣ , prec ⟩ = sim-app vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq vM′ in
  ⟨ Σ , Σ′ , N , μ , ♣ , prec , μ⊑μ′ , size-eq ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-cast v vc′† 𝓋 x vc″ x₁ x₂) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-blame-pc v vc′† 𝓋 x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-blame v vc′† 𝓋 x vc″ x₁) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-cast v vc′† 𝓋 _ _ _ _) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-blame-pc v vc′† 𝓋 _) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-blame v vc′† 𝓋 _ _ _) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-if-true vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-if-false vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if-true-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if-false-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if!-true-cast vc′† 𝓋) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if!-false-cast vc′† 𝓋) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-let x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref v x) = {!!}

{- ref? -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-ref? {T = T} {T′} {ℓ} M⊑V′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref? {n = n} v′ fresh′ ↠PC′₁ vc′₁)
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ V , v , M↠V , V⊑V′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-ref PC⊑PC′ vc vc′ ↠PC′₁ vc′₁ in
  let fresh = size-eq-fresh size-eq fresh′ in
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , cons-Σ (a⟦ ℓ ⟧ n) T′ Σ′ , _ , cons-μ (a⟦ ℓ ⟧ n) _ v μ ,
    trans-mult (plug-cong (ref?⟦ _ ⟧□ _) M↠V)
               (_ ∣ _ ∣ _ —→⟨ ref? v fresh ↠PC₁ vc₁ ⟩ _ ∣ _ ∣ _ ∎) ,
    ⊑-addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ′) ,
    ⊑μ-new Σ⊑Σ′ μ⊑μ′ (value-⊑-pc V⊑V′ v v′) v v′ fresh fresh′ ,
    size-eq-cons {v = v} {v′} {n} {ℓ} size-eq ⟩

sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref?-blame-pc v x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩

{- deref -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref {v = v′} μ′a≡V′) =
  let ⟨ N , ♣ , prec ⟩ = sim-deref vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq v′ μ′a≡V′ in
  ⟨ Σ , Σ′ , N , μ , ♣ , prec , μ⊑μ′ , size-eq ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref!-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-assign v) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign-cast v 𝓋 x w) = {!!}
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign-blame v 𝓋 x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩

{- assign?-cast -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast v′ vc′† 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′)
    rewrite uniq-LVal vc′† vc′ =
    ⟨ Σ , Σ′ , sim-assign?-cast vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq  v′ 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′ ⟩

sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast-blame-pc v vc′† 𝓋 x) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim {Σ} {Σ′} {μ₁ = μ} vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast-blame v vc′† 𝓋 x x₁ x₂) =
  let ⟨ ⊢M , _ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ M⊑M′ in
  ⟨ Σ , Σ′ , _ , _ , _ ∣ _ ∣ _ ∎ , ⊑-blame ⊢M A⊑A′ , μ⊑μ′ , size-eq ⟩
sim vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′
  with sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′
... | ⟨ Σ₂ , Σ₂′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
  ⟨ Σ₂ , Σ₂′ , N ⟨ c ⟩ , μ₂ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ₂⊑μ₂′ , size-eq′ ⟩
