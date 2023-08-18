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


-- data _;_;_⊢_⊑_ : ∀ (Σ Σ′ : HeapContext) → ∀ ℓ → (μ μ′ : HalfHeap) → Set where

--   ⊑-∅ : ∀ {Σ Σ′ ℓ} → Σ ; Σ′ ; ℓ ⊢ [] ⊑ []

--   ⊑-∷ : ∀ {Σ Σ′ ℓ} {μ μ′ n} {V V′} {T T′}
--     → Σ ; Σ′ ; ℓ ⊢ μ ⊑ μ′
--     → [] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ V′ ⇐ T of l ℓ ⊑ T′ of l ℓ
--     → (v  : Value V )
--     → (v′ : Value V′)
--     → lookup-Σ Σ  (a⟦ ℓ ⟧ n) ≡ just T
--     → lookup-Σ Σ′ (a⟦ ℓ ⟧ n) ≡ just T′
--     → n < 1 + length μ
--     → n < 1 + length μ′
--       --------------------------------------------------------------------------------
--     → Σ ; Σ′ ; ℓ ⊢ (⟨ n , V & v ⟩ ∷ μ) ⊑ (⟨ n , V′ & v′ ⟩ ∷ μ′)

-- _;_⊢_⊑_ : ∀ (Σ Σ′ : HeapContext) (μ μ′ : Heap) → Set
-- Σ ; Σ′ ⊢ ⟨ μᴸ , μᴴ ⟩ ⊑ ⟨ μᴸ′ , μᴴ′ ⟩ = (Σ ; Σ′ ; low ⊢ μᴸ ⊑ μᴸ′) × (Σ ; Σ′ ; high ⊢ μᴴ ⊑ μᴴ′)

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

postulate
  prec-relax-Σ : ∀ {Σ₁ Σ₂ Σ₁′ Σ₂′} {A B} {M N}
    → [] ; [] ∣ Σ₁ ; Σ₁′ ∣ l low ; l low ∣ low ; low ⊢ M ⊑ N ⇐ A ⊑ B
    → Σ₂  ⊇ Σ₁
    → Σ₂′ ⊇ Σ₁′
      -----------------------------
    → [] ; [] ∣ Σ₂ ; Σ₂′ ∣ l low ; l low ∣ low ; low ⊢ M ⊑ N ⇐ A ⊑ B
-- prec-relax-Σ {Σ₁} {Σ₂} {Σ₁′} {Σ₂′} M⊑N Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ = {!!}

-- (⊑-addr {n = n} {ℓ} {ℓ̂} a b) (V-raw V-addr) (V-raw V-addr) Σ₂⊇Σ₁ Σ₂′⊇Σ₁′ =
--   ⊑-addr (Σ₂⊇Σ₁ (a⟦ ℓ̂ ⟧ n) a) (Σ₂′⊇Σ₁′ (a⟦ ℓ̂ ⟧ n) b)
-- prec-relax-Σ (⊑-lam x y z) (V-raw V-ƛ) (V-raw V-ƛ) a b = ⊑-lam x y {!z!}
-- prec-relax-Σ V⊑W (V-raw V-const) (V-raw V-const) a b = {!!}
-- prec-relax-Σ (⊑-castr V⊑W x) (V-raw v) (V-cast w i′) a b =
--   ⊑-castr (prec-relax-Σ V⊑W (V-raw v) (V-raw w) a b) x
-- prec-relax-Σ (⊑-castl V⊑W x) (V-cast v i) (V-raw w) a b =
--   ⊑-castl (prec-relax-Σ V⊑W (V-raw v) (V-raw w) a b) x
-- prec-relax-Σ (⊑-cast V⊑W x) (V-cast v i) (V-cast w i′) a b =
--   ⊑-cast (prec-relax-Σ V⊑W (V-raw v) (V-raw w) a b) x
-- prec-relax-Σ (⊑-castl V⊑W x) (V-cast v i) (V-cast w i′) a b =
--   ⊑-castl (prec-relax-Σ V⊑W (V-raw v) (V-cast w i′) a b) x
-- prec-relax-Σ (⊑-castr V⊑W x) (V-cast v i) (V-cast w i′) a b =
--   ⊑-castr (prec-relax-Σ V⊑W (V-cast v i) (V-raw w) a b) x
-- prec-relax-Σ V⊑W V-● w = contradiction V⊑W (●⋤ _)
-- prec-relax-Σ V⊑W v V-● = contradiction V⊑W (_ ⋤●)


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
⊑μ-new {Σ} {Σ′} {S} {T} {n = n₁} {high} Σ⊑Σ′ μ⊑μ′ V⊑W v w fresh fresh′ n high eq eq′ = {!!}


-- ⊑μ-update : ∀ {Σ Σ′} {S T V W} {μ μ′} {n ℓ}
--   → Σ ; Σ′ ⊢ μ ⊑ μ′
--   → [] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ W ⇐ S of l ℓ ⊑ T of l ℓ
--   → (v : Value V)
--   → (w : Value W)
--   → lookup-Σ Σ  (a⟦ ℓ ⟧ n) ≡ just S  {- updating a -}
--   → lookup-Σ Σ′ (a⟦ ℓ ⟧ n) ≡ just T
--     -------------------------------------------------------------------------
--   → Σ ; Σ′ ⊢ cons-μ (a⟦ ℓ ⟧ n) V v μ ⊑ cons-μ (a⟦ ℓ ⟧ n) W w μ′
-- ⊑μ-update {ℓ = low}  ⟨ μᴸ⊑μᴸ′ , μᴴ⊑μᴴ′ ⟩ V⊑W v w a b = ⟨ ⊑-∷ μᴸ⊑μᴸ′ V⊑W v w a b , μᴴ⊑μᴴ′ ⟩
-- ⊑μ-update {ℓ = high} ⟨ μᴸ⊑μᴸ′ , μᴴ⊑μᴴ′ ⟩ V⊑W v w a b = ⟨ μᴸ⊑μᴸ′ , ⊑-∷ μᴴ⊑μᴴ′ V⊑W v w a b ⟩


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

-- private
--   ⊑μ-length-low : ∀ {Σ Σ′} {μ μ′}
--     → Σ ; Σ′ ; low ⊢ μ ⊑ μ′
--     → length μ′ ≡ length μ
--   ⊑μ-length-low ⊑-∅ = refl
--   ⊑μ-length-low (⊑-∷ μ⊑μ′ _ _ _ _ _) = cong suc (⊑μ-length-low μ⊑μ′)

--   ⊑μ-length-high : ∀ {Σ Σ′} {μ μ′}
--     → Σ ; Σ′ ; high ⊢ μ ⊑ μ′
--     → length μ′ ≡ length μ
--   ⊑μ-length-high ⊑-∅ = refl
--   ⊑μ-length-high (⊑-∷ μ⊑μ′ _ _ _ _ _) = cong suc (⊑μ-length-high μ⊑μ′)

-- ⊑μ-fresh : ∀ {Σ Σ′} {μ μ′} {n ℓ}
--   → Σ ; Σ′ ⊢ μ ⊑ μ′
--   → a⟦ ℓ ⟧ n FreshIn μ′
--     -------------------------------------------------------------------------
--   → a⟦ ℓ ⟧ n FreshIn μ
-- ⊑μ-fresh {ℓ = low}  ⟨ μ⊑μ′ , _ ⟩ fresh rewrite ⊑μ-length-low  μ⊑μ′ = fresh
-- ⊑μ-fresh {ℓ = high} ⟨ _ , μ⊑μ′ ⟩ fresh rewrite ⊑μ-length-high μ⊑μ′ = fresh
