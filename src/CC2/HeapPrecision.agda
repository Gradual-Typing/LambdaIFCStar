open import Common.Types

module CC2.HeapPrecision where

open import Data.Nat
open import Data.Nat.Properties using (n≮n; <-trans; n<1+n; ≤-refl)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax hiding (_⨟_)
open import Common.Utils
open import CC2.Statics
open import CC2.Precision
open import CC2.HeapTyping


_;_⊢_⊑_ : ∀ (Σ Σ′ : HeapContext) (μ μ′ : Heap) → Set
Σ ; Σ′ ⊢ μ ⊑ μ′ = ∀ n ℓ {T T′}
  → lookup-Σ Σ  (a⟦ ℓ ⟧ n) ≡ just T
  → lookup-Σ Σ′ (a⟦ ℓ ⟧ n) ≡ just T′
    ---------------------------------
  → (WFAddr a⟦ ℓ ⟧ n In μ ) ×
     (WFAddr a⟦ ℓ ⟧ n In μ′) ×
     (∃[ V ] ∃[ v ] ∃[ V′ ] ∃[ v′ ]
       lookup-μ μ  (a⟦ ℓ ⟧ n) ≡ just (V  & v ) ×
       lookup-μ μ′ (a⟦ ℓ ⟧ n) ≡ just (V′ & v′) ×
       [] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ V′ ⇐ T of l ℓ ⊑ T′ of l ℓ)



⊑μ→⊢μ : ∀ {Σ Σ′} {μ μ′}
  → Σ ⊑ₘ Σ′
  → Σ ; Σ′ ⊢ μ ⊑ μ′
   -----------------------------
  → Σ ⊢ μ × Σ′ ⊢ μ′
⊑μ→⊢μ {Σ} {Σ′} {μ} {μ′} Σ⊑Σ′ μ⊑μ′ = ⟨ ⊢μ , ⊢μ′ ⟩
  where
  ⊢μ : Σ ⊢ μ
  ⊢μ n ℓ Σa≡T =
    let ⟨ T′ , Σ′a≡T′ , T⊑T′ ⟩ = ⊑ₘ→⊑-forward {n = n} {ℓ} Σ⊑Σ′ Σa≡T in
    let ⟨ wf , wf′ , V , v , V′ , v′ , μa≡V , μ′a≡V′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ Σa≡T Σ′a≡T′ in
    let ⟨ ⊢V , ⊢V′ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ V⊑V′ in
    ⟨ wf , V , v , μa≡V , ⊢V ⟩
  ⊢μ′ : Σ′ ⊢ μ′
  ⊢μ′ n ℓ Σ′a≡T′ =
    let ⟨ T , Σa≡T , T⊑T′ ⟩ = ⊑ₘ→⊑-backward {n = n} {ℓ} Σ⊑Σ′ Σ′a≡T′ in
    let ⟨ wf , wf′ , V , v , V′ , v′ , μa≡V , μ′a≡V′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ Σa≡T Σ′a≡T′ in
    let ⟨ ⊢V , ⊢V′ , A⊑A′ ⟩ = cc-prec-inv ⊑*-∅ Σ⊑Σ′ V⊑V′ in
    ⟨ wf′ , V′ , v′ , μ′a≡V′ , ⊢V′ ⟩


prec-relax-Σ : ∀ {Γ Γ′ Σ₁ Σ₂ Σ₁′ Σ₂′ gc gc′ ℓv ℓv′} {A B} {M N}
  → Γ ; Γ′ ∣ Σ₁ ; Σ₁′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ N ⇐ A ⊑ B
  → Σ₂  ⊇ Σ₁
  → Σ₂′ ⊇ Σ₁′
    -----------------------------
  → Γ ; Γ′ ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ N ⇐ A ⊑ B
prec-relax-Σ (⊑-var x y) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-var x y
prec-relax-Σ ⊑-const Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-const
prec-relax-Σ (⊑-addr {n = n} {ℓ̂ = ℓ̂} eq eq′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-addr (Σ₂⊇Σ₁ (a⟦ ℓ̂ ⟧ n) eq) (Σ₂′⊇Σ₁′ (a⟦ ℓ̂ ⟧ n) eq′)
prec-relax-Σ (⊑-lam g⊑g′ A⊑A′ N⊑N′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-lam g⊑g′ A⊑A′ (prec-relax-Σ N⊑N′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′)
prec-relax-Σ (⊑-app L⊑L′ M⊑M′ x y) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-app (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x y
prec-relax-Σ (⊑-app⋆ L⊑L′ M⊑M′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-app⋆ (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′)
prec-relax-Σ (⊑-app⋆l L⊑L′ M⊑M′ x) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-app⋆l (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x
prec-relax-Σ (⊑-if L⊑L′ M⊑M′ N⊑N′ x y) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-if (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ N⊑N′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x y
prec-relax-Σ (⊑-if⋆ L⊑L′ M⊑M′ N⊑N′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-if⋆ (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ N⊑N′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′)
prec-relax-Σ (⊑-if⋆l L⊑L′ M⊑M′ N⊑N′ x) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-if⋆l (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ N⊑N′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x
prec-relax-Σ (⊑-let M⊑M′ N⊑N′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-let (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ N⊑N′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′)
prec-relax-Σ (⊑-ref M⊑M′ x) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-ref (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x
prec-relax-Σ (⊑-ref? M⊑M′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-ref? (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′)
prec-relax-Σ (⊑-ref?l M⊑M′ x) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-ref?l (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x
prec-relax-Σ (⊑-deref M⊑M′ x y) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-deref (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x y
prec-relax-Σ (⊑-deref⋆ M⊑M′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-deref⋆ (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′)
prec-relax-Σ (⊑-deref⋆l M⊑M′ x) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-deref⋆l (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x
prec-relax-Σ (⊑-assign L⊑L′ M⊑M′ x y) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-assign (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x y
prec-relax-Σ (⊑-assign? L⊑L′ M⊑M′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-assign? (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′)
prec-relax-Σ (⊑-assign?l L⊑L′ M⊑M′ x y) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-assign?l (prec-relax-Σ L⊑L′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) x y
prec-relax-Σ (⊑-prot M⊑M′ PC⊑PC′ x y eq eq′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-prot (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) PC⊑PC′ x y eq eq′
prec-relax-Σ (⊑-prot! M⊑M′ PC⊑PC′ x y z) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-prot! (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) PC⊑PC′ x y z
prec-relax-Σ (⊑-prot!l M⊑M′ PC⊑PC′ x y eq′ z) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
  ⊑-prot!l (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) PC⊑PC′ x y eq′ z
prec-relax-Σ (⊑-cast M⊑M′ c⊑c′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-cast (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) c⊑c′
prec-relax-Σ (⊑-castl M⊑M′ c⊑A′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-castl (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) c⊑A′
prec-relax-Σ (⊑-castr M⊑M′ A⊑c′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-castr (prec-relax-Σ M⊑M′ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′) A⊑c′
prec-relax-Σ (⊑-blame ⊢M A⊑A′) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = ⊑-blame (relax-Σ ⊢M Σ₂⊇Σ₁) A⊑A′


⊑μ-new : ∀ {Σ Σ′} {S T V W} {μ μ′} {n ℓ}
  → Σ ⊑ₘ Σ′
  → Σ ; Σ′ ⊢ μ ⊑ μ′
  → [] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ S of l ℓ ⊑ T of l ℓ
  → (v : Value V)
  → (w : Value W)
  → a⟦ ℓ ⟧ n FreshIn μ
  → a⟦ ℓ ⟧ n FreshIn μ′
    -------------------------------------------------------------------------
  → cons-Σ (a⟦ ℓ ⟧ n) S Σ   ; cons-Σ (a⟦ ℓ ⟧ n) T Σ′   ⊢
     cons-μ (a⟦ ℓ ⟧ n) V v μ ⊑ cons-μ (a⟦ ℓ ⟧ n) W w μ′
⊑μ-new {Σ} {Σ′} {S} {T} {V} {W} {μ} {μ′} {n₁} {low}
       Σ⊑Σ′ μ⊑μ′ V⊑W v w n₁-fresh n₁-fresh′ n low eq eq′
  with n ≟ n₁
... | yes refl =
  let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
  let Σ₂⊇Σ₁   = ⊇-fresh (a⟦ low ⟧ n) S ⊢μ  n₁-fresh  in
  let Σ₂′⊇Σ₁′ = ⊇-fresh (a⟦ low ⟧ n) T ⊢μ′ n₁-fresh′ in
  case ⟨ eq , eq′ ⟩ of λ where
    ⟨ refl , refl ⟩ →
      ⟨ wfᴸ n₁<1+len , wfᴸ n₁<1+len′ ,
        V , v , W , w , refl , refl ,
        prec-relax-Σ V⊑W Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ ⟩
  where
  n₁<1+len : n₁ < 1 + (length (proj₁ μ))
  n₁<1+len rewrite n₁-fresh = ≤-refl
  n₁<1+len′ : n₁ < 1 + (length (proj₁ μ′))
  n₁<1+len′ rewrite n₁-fresh′ = ≤-refl
... | no _ =
  let ⟨ wf , wf′ , V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ , V₁⊑W₁ ⟩ = μ⊑μ′ n low eq eq′ in
  let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
  let Σ₂⊇Σ₁   = ⊇-fresh (a⟦ low ⟧ n₁) S ⊢μ  n₁-fresh  in
  let Σ₂′⊇Σ₁′ = ⊇-fresh (a⟦ low ⟧ n₁) T ⊢μ′ n₁-fresh′ in
  ⟨ wf-relaxᴸ V v wf , wf-relaxᴸ W w wf′ ,
    V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ ,
    prec-relax-Σ V₁⊑W₁ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ ⟩
⊑μ-new {Σ} {Σ′} {S} {T} {V} {W} {μ} {μ′} {n₁} {low}
       Σ⊑Σ′ μ⊑μ′ V⊑W v w fresh fresh′ n high eq eq′ =
  case μ⊑μ′ n high eq eq′ of λ where
  ⟨ wfᴴ n<len , wfᴴ n<len′ , V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ , V₁⊑W₁ ⟩ →
    let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
    let Σ₂⊇Σ₁   = ⊇-fresh (a⟦ low ⟧ n₁) S ⊢μ  fresh  in
    let Σ₂′⊇Σ₁′ = ⊇-fresh (a⟦ low ⟧ n₁) T ⊢μ′ fresh′ in
    ⟨ wfᴴ n<len , wfᴴ n<len′ ,
      V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ ,
      prec-relax-Σ V₁⊑W₁ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ ⟩
⊑μ-new {Σ} {Σ′} {S} {T} {n = n₁} {high} Σ⊑Σ′ μ⊑μ′ V⊑W v w fresh fresh′ n low eq eq′ =
  case μ⊑μ′ n low eq eq′ of λ where
  ⟨ wfᴸ n<len , wfᴸ n<len′ , V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ , V₁⊑W₁ ⟩ →
    let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
    let Σ₂⊇Σ₁   = ⊇-fresh (a⟦ high ⟧ n₁) S ⊢μ  fresh  in
    let Σ₂′⊇Σ₁′ = ⊇-fresh (a⟦ high ⟧ n₁) T ⊢μ′ fresh′ in
    ⟨ wfᴸ n<len , wfᴸ n<len′ ,
      V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ ,
      prec-relax-Σ V₁⊑W₁ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ ⟩
⊑μ-new {Σ} {Σ′} {S} {T} {V} {W} {μ} {μ′} {n₁} {high}
       Σ⊑Σ′ μ⊑μ′ V⊑W v w fresh fresh′ n high eq eq′
  with n ≟ n₁
... | yes refl =
  let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
  let Σ₂⊇Σ₁   = ⊇-fresh (a⟦ high ⟧ n) S ⊢μ  fresh  in
  let Σ₂′⊇Σ₁′ = ⊇-fresh (a⟦ high ⟧ n) T ⊢μ′ fresh′ in
  case ⟨ eq , eq′ ⟩ of λ where
    ⟨ refl , refl ⟩ →
      ⟨ wfᴴ n₁<1+len , wfᴴ n₁<1+len′ ,
        V , v , W , w , refl , refl ,
        prec-relax-Σ V⊑W Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ ⟩
  where
  n₁<1+len : n₁ < 1 + (length (proj₂ μ))
  n₁<1+len rewrite fresh = ≤-refl
  n₁<1+len′ : n₁ < 1 + (length (proj₂ μ′))
  n₁<1+len′ rewrite fresh′ = ≤-refl
... | no _ =
  let ⟨ wf , wf′ , V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ , V₁⊑W₁ ⟩ = μ⊑μ′ n high eq eq′ in
  let ⟨ ⊢μ , ⊢μ′ ⟩ = ⊑μ→⊢μ Σ⊑Σ′ μ⊑μ′ in
  let Σ₂⊇Σ₁   = ⊇-fresh (a⟦ high ⟧ n₁) S ⊢μ  fresh  in
  let Σ₂′⊇Σ₁′ = ⊇-fresh (a⟦ high ⟧ n₁) T ⊢μ′ fresh′ in
  ⟨ wf-relaxᴴ V v wf , wf-relaxᴴ W w wf′ ,
    V₁ , v₁ , W₁ , w₁ , eq₁ , eq₁′ ,
    prec-relax-Σ V₁⊑W₁ Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ ⟩


⊑μ-update : ∀ {Σ Σ′} {S T V V′} {μ μ′} {n ℓ}
  → Σ ; Σ′ ⊢ μ ⊑ μ′
  → [] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ V′ ⇐ S of l ℓ ⊑ T of l ℓ
  → (v  : Value V )
  → (v′ : Value V′)
  → lookup-Σ Σ  (a⟦ ℓ ⟧ n) ≡ just S  {- updating a -}
  → lookup-Σ Σ′ (a⟦ ℓ ⟧ n) ≡ just T
    -------------------------------------------------------------------------
  → Σ ; Σ′ ⊢ cons-μ (a⟦ ℓ ⟧ n) V v μ ⊑ cons-μ (a⟦ ℓ ⟧ n) V′ v′ μ′
⊑μ-update {n = n₁} {low}  μ⊑μ′ V⊑V′ v v′ eq₁ eq₁′ n low eq eq′
  with n ≟ n₁
... | yes refl =
  case ⟨ trans (sym eq) eq₁ , trans (sym eq′) eq₁′ ⟩ of λ where
  ⟨ refl , refl ⟩ →
    let ⟨ wf , wf′ , W , w , W′ , w′ , eq₂ , eq₂′ , W⊑W′ ⟩ = μ⊑μ′ n low eq eq′ in
    ⟨ wf-relaxᴸ _ v wf , wf-relaxᴸ _ v′ wf′ , _ , v , _ , v′ , refl , refl , V⊑V′ ⟩
... | no  _ =
  let ⟨ wf , wf′ , rest ⟩ = μ⊑μ′ n low eq eq′ in
  ⟨ wf-relaxᴸ _ v wf , wf-relaxᴸ _ v′ wf′ , rest ⟩
⊑μ-update {n = n₁} {low}  μ⊑μ′ V⊑V′ v v′ eq₁ eq₁′ n high eq eq′ =
  case μ⊑μ′ n high eq eq′ of λ where
  ⟨ wfᴴ x , wfᴴ y , rest ⟩ → ⟨ wfᴴ x , wfᴴ y , rest ⟩
⊑μ-update {n = n₁} {high} μ⊑μ′ V⊑V′ v v′ eq₁ eq₁′ n low eq eq′ =
  case μ⊑μ′ n low eq eq′ of λ where
  ⟨ wfᴸ x , wfᴸ y , rest ⟩ → ⟨ wfᴸ x , wfᴸ y , rest ⟩
⊑μ-update {n = n₁} {high} μ⊑μ′ V⊑V′ v v′ eq₁ eq₁′ n high eq eq′
  with n ≟ n₁
... | yes refl =
  case ⟨ trans (sym eq) eq₁ , trans (sym eq′) eq₁′ ⟩ of λ where
  ⟨ refl , refl ⟩ →
    let ⟨ wf , wf′ , W , w , W′ , w′ , eq₂ , eq₂′ , W⊑W′ ⟩ = μ⊑μ′ n high eq eq′ in
    ⟨ wf-relaxᴴ _ v wf , wf-relaxᴴ _ v′ wf′ , _ , v , _ , v′ , refl , refl , V⊑V′ ⟩
... | no  _ =
  let ⟨ wf , wf′ , rest ⟩ = μ⊑μ′ n high eq eq′ in
  ⟨ wf-relaxᴴ _ v wf , wf-relaxᴴ _ v′ wf′ , rest ⟩

size-eq-cons : ∀ {μ μ′} {V W v w} {n ℓ}
  → SizeEq μ μ′
    ----------------------------------------------------------------
  → SizeEq (cons-μ (a⟦ ℓ ⟧ n) V v μ) (cons-μ (a⟦ ℓ ⟧ n) W w μ′)
size-eq-cons {μ = ⟨ μᴸ , μᴴ ⟩} {⟨ μᴸ′ , μᴴ′ ⟩} {ℓ = low}  ⟨ eq-low , eq-high ⟩ =
  ⟨ cong suc eq-low , eq-high ⟩
size-eq-cons {μ = ⟨ μᴸ , μᴴ ⟩} {⟨ μᴸ′ , μᴴ′ ⟩} {ℓ = high} ⟨ eq-low , eq-high ⟩ =
  ⟨ eq-low , cong suc eq-high ⟩


-- private
--   ⊑μ-lookup-low : ∀ {Σ Σ′ T T′} {W w} {μ μ′} {n}
--     → Σ ; Σ′ ; low ⊢ μ ⊑ μ′
--     → find _≟_ μ′ n ≡ just (W & w)
--     → lookup-Σ Σ  (a⟦ low ⟧ n) ≡ just T
--     → lookup-Σ Σ′ (a⟦ low ⟧ n) ≡ just T′
--       ---------------------------------------------------------------------------------------
--     → ∃[ V ] ∃[ v ] (find _≟_ μ n ≡ just (V & v)) ×
--          ([] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ T of l low ⊑ T′ of l low)
--   ⊑μ-lookup-low {T = T} {T′} {w = w} {n = n}
--                 (⊑-∷ {n = m} {V} {V′} {S} {S′} μ⊑μ′ V⊑V′ v v′ Σa≡S Σ′a≡S′) eq Σa≡T Σ′a≡T′
--     with n ≟ m
--   ... | no _ = ⊑μ-lookup-low {w = w} μ⊑μ′ eq Σa≡T Σ′a≡T′
--   ... | yes refl
--     with trans (sym Σa≡T) Σa≡S | trans (sym Σ′a≡T′) Σ′a≡S′ | eq
--   ...   | refl | refl | refl = ⟨ V , v , refl , V⊑V′ ⟩

--   ⊑μ-lookup-high : ∀ {Σ Σ′ T T′} {W w} {μ μ′} {n}
--     → Σ ; Σ′ ; high ⊢ μ ⊑ μ′
--     → find _≟_ μ′ n ≡ just (W & w)
--     → lookup-Σ Σ  (a⟦ high ⟧ n) ≡ just T
--     → lookup-Σ Σ′ (a⟦ high ⟧ n) ≡ just T′
--       ---------------------------------------------------------------------------------------
--     → ∃[ V ] ∃[ v ] (find _≟_ μ n ≡ just (V & v)) ×
--          ([] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ T of l high ⊑ T′ of l high)
--   ⊑μ-lookup-high {T = T} {T′} {w = w} {n = n}
--                 (⊑-∷ {n = m} {V} {V′} {S} {S′} μ⊑μ′ V⊑V′ v v′ Σa≡S Σ′a≡S′) eq Σa≡T Σ′a≡T′
--     with n ≟ m
--   ... | no _ = ⊑μ-lookup-high {w = w} μ⊑μ′ eq Σa≡T Σ′a≡T′
--   ... | yes refl
--     with trans (sym Σa≡T) Σa≡S | trans (sym Σ′a≡T′) Σ′a≡S′ | eq
--   ...   | refl | refl | refl = ⟨ V , v , refl , V⊑V′ ⟩

-- ⊑μ-lookup : ∀ {Σ Σ′ S T} {W w} {μ μ′} {ℓ n}
--   → Σ ; Σ′ ⊢ μ ⊑ μ′
--   → lookup-μ μ′ (a⟦ ℓ ⟧ n) ≡ just (W & w)
--   → lookup-Σ Σ  (a⟦ ℓ ⟧ n) ≡ just S
--   → lookup-Σ Σ′ (a⟦ ℓ ⟧ n) ≡ just T
--     ------------------------------------------------------------------------------------
--   → ∃[ V ] ∃[ v ] (lookup-μ μ (a⟦ ℓ ⟧ n) ≡ just (V & v)) ×
--         ([] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ S of l ℓ ⊑ T of l ℓ)
-- ⊑μ-lookup {w = w} {ℓ = low}  ⟨ μ⊑μ′ , _ ⟩ = ⊑μ-lookup-low  {w = w} μ⊑μ′
-- ⊑μ-lookup {w = w} {ℓ = high} ⟨ _ , μ⊑μ′ ⟩ = ⊑μ-lookup-high {w = w} μ⊑μ′
