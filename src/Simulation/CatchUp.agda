module Simulation.CatchUp where

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

open import Common.Utils
open import Memory.HeapContext
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CoercionExpr.Precision
open import CoercionExpr.CatchUp renaming (catchup to catchupₗ)
open import CoercionExpr.SyntacComp

catchup : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M V′ μ PC} {A A′}
  → Value V′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ V′ ⇐ A ⊑ A′
    -------------------------------------------------------------------
  → ∃[ V ] (Value V) ×
       (M ∣ μ ∣ PC —↠ V ∣ μ) ×
       (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′)
catchup (V-raw V-const) ⊑-const  = ⟨ _ , V-raw V-const , _ ∣ _ ∣ _ ∎ , ⊑-const ⟩
catchup (V-raw V-addr) (⊑-addr x y) = ⟨ _ , V-raw V-addr , _ ∣ _ ∣ _ ∎ , ⊑-addr x y ⟩
catchup (V-raw V-ƛ) (⊑-lam g⊑g′ A⊑A′ N⊑N′) = ⟨ _ , V-raw V-ƛ , _ ∣ _ ∣ _ ∎ , ⊑-lam g⊑g′ A⊑A′ N⊑N′ ⟩
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-raw v′) (⊑-castl {c = c} M⊑V′ c⊑A′)
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′
... | ⟨ V , V-raw V-const , M↠V , ⊑-const ⟩ =
  case c⊑A′ of λ where
  (⊑-base c̅⊑g′) →
    case catchupₗ _ _ CVal.id (⊑-left-expand c̅⊑g′) of λ where
    ⟨ _ , id , _ ∎ₗ , id⊑id ⟩ →
      ⟨ _ , V-raw V-const ,
        trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩ _ ∣ _ ∣ _ ∎) ,
        ⊑-const ⟩
    ⟨ _ , id , _ —→ₗ⟨ r ⟩ r* , id⊑id ⟩ →
      ⟨ _ , V-raw V-const ,
        trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) CVal.id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-const ⟩
    ⟨ _ , inj 𝓋 , _ ∎ₗ , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩ →
      ⟨ _ , V-cast V-const (ir-base (inj 𝓋) (λ ())) ,
        plug-cong (□⟨ _ ⟩) M↠V ,
        ⊑-castl ⊑-const (⊑-base (⊑-cast (⊑-left-contract c̅ₙ⊑id) l⊑l ⋆⊑)) ⟩
    ⟨ _ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩ →
      ⟨ _ , V-cast V-const (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl ⊑-const (⊑-base (⊑-cast (⊑-left-contract c̅ₙ⊑id) l⊑l ⋆⊑)) ⟩
    ⟨ _ , up id , c̅↠↑ , ⊑-castl _ _ () ⟩  {- impossible -}
... | ⟨ V , V-raw V-ƛ , M↠V , ⊑-lam g⊑g′ A⊑A′ N⊑N′ ⟩ =
  case c⊑A′ of λ where
  (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) →
    case catchupₗ _ _ CVal.id (⊑-left-expand c̅⊑g′) of λ where
    ⟨ c̅ₙ , 𝓋 , _ ∎ₗ , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast V-ƛ (ir-fun 𝓋) ,
        plug-cong (□⟨ _ ⟩) M↠V ,
        ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
    ⟨ c̅ₙ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast V-ƛ (ir-fun 𝓋) ,
        trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-ƛ) (cast V-ƛ (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ V , V-raw V-addr , M↠V , ⊑-addr x y ⟩ =
  case c⊑A′ of λ where
  (⊑-ref c⊑A′ d⊑B′ c̅⊑g′) →
    case catchupₗ _ _ CVal.id (⊑-left-expand c̅⊑g′) of λ where
    ⟨ c̅ₙ , 𝓋 , _ ∎ₗ , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast V-addr (ir-ref 𝓋) ,
        plug-cong (□⟨ _ ⟩) M↠V ,
        ⊑-castl (⊑-addr x y) (⊑-ref c⊑A′ d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
    ⟨ c̅ₙ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast V-addr (ir-ref 𝓋) ,
        trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-addr) (cast V-addr (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-addr x y) (⊑-ref c⊑A′ d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ V ⟨ cast _ d̅ ⟩ , V-cast v i , M↠V , ⊑-castl ⊑-const d⊑A′ ⟩ =
  case ⟨ d⊑A′ , c⊑A′ ⟩ of λ where
  ⟨ ⊑-base d̅⊑g′ , ⊑-base c̅⊑g′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll d̅⊑g′ c̅⊑g′)) of λ where
    ⟨ _ , id , d̅⨟c̅↠id , id⊑id ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠id id) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-const ⟩
    ⟨ _ , inj 𝓋 , d̅⨟c̅↠! , !⊑id ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠! (inj 𝓋)) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl ⊑-const (⊑-base (⊑-left-contract !⊑id)) ⟩
    ⟨ _ , up id , d̅⨟c̅↠↑ , ↑⊑id ⟩ →
      ⟨ _ , V-cast v (ir-base (up id) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠↑ (up id)) (up id)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl ⊑-const (⊑-base (⊑-left-contract ↑⊑id)) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) d⊑A′ ⟩ =
  case ⟨ d⊑A′ , c⊑A′ ⟩ of λ where
  ⟨ ⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑g′ c̅⊑g′)) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
      let d̅⨟d̅₁⊑gc′ = comp-pres-⊑-ll d̅⊑gc′ d̅₁⊑gc′ in
      let c⨟c₁⊑A′ = comp-pres-prec-ll c⊑A′ c₁⊑A′ in
      let d₁⨟d⊑B′ = comp-pres-prec-ll d₁⊑B′ d⊑B′ in
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′)
                (⊑-fun d̅⨟d̅₁⊑gc′ c⨟c₁⊑A′ d₁⨟d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-addr x y) d⊑A′ ⟩ =
  case ⟨ d⊑A′ , c⊑A′ ⟩ of λ where
  ⟨ ⊑-ref c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-ref c⊑A′ d⊑B′ c̅⊑g′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑g′ c̅⊑g′)) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
      let c⨟c₁⊑A′ = comp-pres-prec-ll c⊑A′ c₁⊑A′ in
      let d₁⨟d⊑B′ = comp-pres-prec-ll d₁⊑B′ d⊑B′ in
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-addr x y)
                (⊑-ref c⨟c₁⊑A′ d₁⨟d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ ● , V-● , M↠● , ●⊑V′ ⟩ = contradiction ●⊑V′ (●⋤ _)
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-cast v′ i′) (⊑-cast {c = c} M⊑V′ c⊑c′)
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′
... | ⟨ V , V-raw v , M↠V , ⊑-const ⟩ =
  case ⟨ c⊑c′ , i′ ⟩ of λ where
  ⟨ ⊑-base c̅⊑c̅′ , ir-base 𝓋′ _ ⟩ →
    case catchupₗ _ _ 𝓋′ c̅⊑c̅′ of λ where
    ⟨ _ , id , _ ∎ₗ , id⊑c̅′ ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const (⊑-base (⊑-right-contract id⊑c̅′)) ⟩
    ⟨ _ , id , _ —→ₗ⟨ r ⟩ r* , id⊑c̅′ ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const (⊑-base (⊑-right-contract id⊑c̅′)) ⟩
    ⟨ _ , inj 𝓋 , _ ∎ₗ , !⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        plug-cong □⟨ _ ⟩ M↠V ,
        ⊑-cast ⊑-const (⊑-base !⊑c̅′) ⟩
    ⟨ _ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , !⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base !⊑c̅′) ⟩
    ⟨ _ , up id , _ ∎ₗ , ↑⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (up id) (λ ())) ,
        plug-cong □⟨ _ ⟩ M↠V ,
        ⊑-cast ⊑-const (⊑-base ↑⊑c̅′) ⟩
    ⟨ _ , up id , _ —→ₗ⟨ r ⟩ r* , ↑⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (up id) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) (up id)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base ↑⊑c̅′) ⟩
... | ⟨ V , V-raw v , M↠V , ⊑-lam x y z ⟩ =
  case ⟨ c⊑c′ , i′ ⟩ of λ where
  ⟨ ⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ , ir-fun 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ c̅⊑c̅′ of λ where
    ⟨ _ , 𝓋 , _ ∎ₗ , c̅ₙ⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        plug-cong □⟨ _ ⟩ M↠V ,
        ⊑-cast (⊑-lam x y z) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′) ⟩
    ⟨ _ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-lam x y z) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅ₙ⊑c̅′) ⟩
... | ⟨ V , V-raw v , M↠V , ⊑-addr x y ⟩ =
  case ⟨ c⊑c′ , i′ ⟩ of λ where
  ⟨ ⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′ , ir-ref 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ c̅⊑c̅′ of λ where
    ⟨ _ , 𝓋 , _ ∎ₗ , c̅ₙ⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        plug-cong □⟨ _ ⟩ M↠V ,
        ⊑-cast (⊑-addr x y) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) ⟩
    ⟨ _ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-addr x y) (⊑-ref c⊑c′ d⊑d′ c̅ₙ⊑c̅′) ⟩
... | ⟨ V ⟨ c₁ ⟩ , V-cast v i , M↠V , ⊑-castl ⊑-const c₁⊑A′ ⟩ =
  case ⟨ c₁⊑A′ , c⊑c′ , i′ ⟩ of λ where
  ⟨ ⊑-base d̅⊑g′ , ⊑-base c̅⊑c̅′ , ir-base 𝓋′ _ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-lb d̅⊑g′ c̅⊑c̅′) of λ where
    ⟨ _ , id , d̅⨟c̅↠id , id⊑c̅′ ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠id id) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const (⊑-base (⊑-right-contract id⊑c̅′)) ⟩
    ⟨ _ , inj 𝓋 , d̅⨟c̅↠! , !⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠! (inj 𝓋)) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base !⊑c̅′) ⟩
    ⟨ _ , up id , d̅⨟c̅↠↑ , ↑⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (up id) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠↑ (up id)) (up id)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base ↑⊑c̅′) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) c₁⊑A′ ⟩ =
  case ⟨ c₁⊑A′ , c⊑c′ , i′ ⟩ of λ where
  ⟨ ⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ , ir-fun 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-lb c̅₁⊑g′ c̅⊑c̅′) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
      let d̅⨟d̅₁⊑d̅′ = comp-pres-⊑-bl d̅⊑d̅′ d̅₁⊑gc′ in
      let c⨟c₁⊑c′ = comp-pres-prec-bl c⊑c′ c₁⊑A′ in
      let d₁⨟d⊑d′ = comp-pres-prec-lb d₁⊑B′ d⊑d′ in
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⨟d̅₁⊑d̅′ c⨟c₁⊑c′ d₁⨟d⊑d′ c̅ₙ⊑c̅′) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-addr x y) c₁⊑A′ ⟩ =
  case ⟨ c₁⊑A′ , c⊑c′ , i′ ⟩ of λ where
  ⟨ ⊑-ref c₁⊑A′ d₁⊑A′ c̅₁⊑g′ , ⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′ , ir-ref 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-lb c̅₁⊑g′ c̅⊑c̅′) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
      let c⨟c₁⊑c′ = comp-pres-prec-bl c⊑c′ c₁⊑A′ in
      let d₁⨟d⊑d′ = comp-pres-prec-lb d₁⊑A′ d⊑d′ in
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-addr x y) (⊑-ref c⨟c₁⊑c′ d₁⨟d⊑d′ c̅ₙ⊑c̅′) ⟩
... | ⟨ ● , V-● , M↠● , ●⊑V′ ⟩ = contradiction ●⊑V′ (●⋤ _)
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-cast v′ i′) (⊑-castl {c = c} M⊑V′ c⊑A′)
  with catchup {μ = μ} {PC} (V-cast v′ i′) M⊑V′
... | ⟨ V , V-raw v , M↠V , ⊑-castr ⊑-const A⊑c′ ⟩ =
  case c⊑A′ of λ where
  (⊑-base c̅⊑g′) →
    case catchupₗ _ _ CVal.id (⊑-left-expand c̅⊑g′) of λ where
    ⟨ _ , id , _ ∎ₗ , id⊑id ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const A⊑c′ ⟩
    ⟨ _ , id , _ —→ₗ⟨ r ⟩ r* , id⊑id ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const A⊑c′ ⟩
    ⟨ _ , inj 𝓋 , _ ∎ₗ , !⊑id ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        plug-cong □⟨ _ ⟩ M↠V ,
        ⊑-castl (⊑-castr ⊑-const A⊑c′) (⊑-base (⊑-left-contract !⊑id)) ⟩
    ⟨ _ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , !⊑id ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-castr ⊑-const A⊑c′) (⊑-base (⊑-left-contract !⊑id)) ⟩
    ⟨ _ , up id , d̅⨟c̅↠↑ , ⊑-castl _ l⊑l () ⟩
... | ⟨ V , V-raw v , M↠V , ⊑-castr (⊑-lam x y z) A⊑c′ ⟩ =
  case c⊑A′ of λ where
  (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) →
    case catchupₗ _ _ CVal.id (⊑-left-expand c̅⊑g′) of λ where
    ⟨ _ , 𝓋 , _ ∎ₗ , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        plug-cong □⟨ _ ⟩ M↠V ,
        ⊑-castl (⊑-castr (⊑-lam x y z) A⊑c′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) ⟩
    ⟨ _ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-castr (⊑-lam x y z) A⊑c′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ V , V-raw v , M↠V , ⊑-castr (⊑-addr x y) A⊑c′ ⟩ =
  case c⊑A′ of λ where
  (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) →
    case catchupₗ _ _ CVal.id (⊑-left-expand c̅⊑g′) of λ where
    ⟨ _ , 𝓋 , _ ∎ₗ , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        plug-cong □⟨ _ ⟩ M↠V ,
        ⊑-castl (⊑-castr (⊑-addr x y) A⊑c′) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩
    ⟨ _ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑id ⟩ →
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (_ —→ₗ⟨ r ⟩ r*) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-castr (⊑-addr x y) A⊑c′) (⊑-ref c⊑A′ d⊑A′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ V ⟨ c₁ ⟩ , V-cast v i , M↠V , ⊑-cast ⊑-const c₁⊑c′ ⟩ =
  case ⟨ c₁⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-base d̅⊑c̅′ , ⊑-base c̅⊑g′ , ir-base 𝓋′ _ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-bl d̅⊑c̅′ c̅⊑g′) of λ where
    ⟨ _ , id , d̅⨟c̅↠id , id⊑c̅′ ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠id id) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const (⊑-base (⊑-right-contract id⊑c̅′)) ⟩
    ⟨ _ , inj 𝓋 , d̅⨟c̅↠! , !⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠! (inj 𝓋)) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base !⊑c̅′) ⟩
    ⟨ _ , up id , d̅⨟c̅↠↑ , ↑⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (up id) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠↑ (up id)) (up id)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base ↑⊑c̅′) ⟩
... | ⟨ V ⟨ c₁ ⟩ , V-cast v i , M↠V , ⊑-castl (⊑-castr ⊑-const A⊑c′) c₁⊑A′ ⟩ =
  case ⟨ c₁⊑A′ , A⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-base d̅⊑g′ , ⊑-base g⊑c̅′ , ⊑-base c̅⊑g′ , ir-base 𝓋′ _ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll d̅⊑g′ c̅⊑g′)) of λ where
    ⟨ _ , id , d̅⨟c̅↠id , id⊑c̅′ ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠id id) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const (⊑-base g⊑c̅′) ⟩
    ⟨ _ , inj 𝓋 , d̅⨟c̅↠! , !⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠! (inj 𝓋)) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-castr ⊑-const (⊑-base g⊑c̅′)) (⊑-base (⊑-left-contract !⊑c̅′)) ⟩
    ⟨ _ , up id , d̅⨟c̅↠↑ , ↑⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (up id) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠↑ (up id)) (up id)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-castr ⊑-const (⊑-base g⊑c̅′)) (⊑-base (⊑-left-contract ↑⊑c̅′)) ⟩
... | ⟨ V ⟨ c₁ ⟩ , V-cast v i , M↠V , ⊑-castr (⊑-castl ⊑-const c₁⊑A′) A⊑c′ ⟩ =
  case ⟨ c₁⊑A′ , A⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-base d̅⊑g′ , ⊑-base g⊑c̅′ , ⊑-base c̅⊑g′ , ir-base 𝓋′ _ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-bl (comp-pres-⊑-lr d̅⊑g′ g⊑c̅′) c̅⊑g′) of λ where
    ⟨ _ , id , d̅⨟c̅↠id , id⊑c̅′ ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠id id) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castr ⊑-const (⊑-base (⊑-right-contract id⊑c̅′)) ⟩
    ⟨ _ , inj 𝓋 , d̅⨟c̅↠! , !⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠! (inj 𝓋)) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base !⊑c̅′) ⟩
    ⟨ _ , up id , d̅⨟c̅↠↑ , ↑⊑c̅′ ⟩ →
      ⟨ _ , V-cast v (ir-base (up id) (λ ())) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠↑ (up id)) (up id)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast ⊑-const (⊑-base ↑⊑c̅′) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) c₁⊑c′ ⟩ =
  case ⟨ c₁⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-fun d̅₁⊑d̅′ c₁⊑c′ d₁⊑d′ c̅₁⊑c̅′ , ⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′ , ir-fun 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-bl c̅₁⊑c̅′ c̅⊑g′) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
      let d̅⨟d̅₁⊑d̅′ = comp-pres-⊑-lb d̅⊑gc′ d̅₁⊑d̅′ in
      let c⨟c₁⊑c′ = comp-pres-prec-lb c⊑A′ c₁⊑c′ in
      let d₁⨟d⊑d′ = comp-pres-prec-bl d₁⊑d′ d⊑B′ in
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⨟d̅₁⊑d̅′ c⨟c₁⊑c′ d₁⨟d⊑d′ c̅ₙ⊑c̅′) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-castr (⊑-lam g⊑g′ A⊑A′ N⊑N′) A⊑c′) c₁⊑A′ ⟩ =
  case ⟨ c₁⊑A′ , A⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′ , ⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′ , ir-fun 𝓋′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑g′ c̅⊑g′)) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
      let d̅⨟d̅₁⊑d̅′ = comp-pres-⊑-lr (comp-pres-⊑-ll d̅⊑gc′ d̅₁⊑gc′) gc⊑d̅′ in
      let c⨟c₁⊑c′ = comp-pres-prec-lr (comp-pres-prec-ll c⊑A′ c₁⊑A′) A⊑c′ in
      let d₁⨟d⊑d′ = comp-pres-prec-rl B⊑d′ (comp-pres-prec-ll d₁⊑B′ d⊑B′) in
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⨟d̅₁⊑d̅′ c⨟c₁⊑c′ d₁⨟d⊑d′ (comp-pres-⊑-rl g⊑c̅′ (⊑-left-contract c̅ₙ⊑id))) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castr (⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) c₁⊑A′) A⊑c′ ⟩ =
  case ⟨ c₁⊑A′ , A⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′ , ⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′ , ir-fun 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-bl (comp-pres-⊑-lr c̅₁⊑g′ g⊑c̅′) c̅⊑g′) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
      let d̅⨟d̅₁⊑d̅′ = comp-pres-⊑-bl (comp-pres-⊑-lr d̅⊑gc′ gc⊑d̅′) d̅₁⊑gc′ in
      let c⨟c₁⊑c′ = comp-pres-prec-bl (comp-pres-prec-lr c⊑A′ A⊑c′) c₁⊑A′ in
      let d₁⨟d⊑d′ = comp-pres-prec-bl (comp-pres-prec-lr d₁⊑B′ B⊑d′) d⊑B′ in
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⨟d̅₁⊑d̅′ c⨟c₁⊑c′ d₁⨟d⊑d′ c̅ₙ⊑c̅ₙ′) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-cast (⊑-addr x y) c₁⊑c′ ⟩ =
  case ⟨ c₁⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-ref c₁⊑c′ d₁⊑d′ c̅₁⊑c̅′ , ⊑-ref c⊑A′ d⊑A′ c̅⊑g′ , ir-ref 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-bl c̅₁⊑c̅′ c̅⊑g′) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅′ ⟩ →
      let c⨟c₁⊑c′ = comp-pres-prec-lb c⊑A′ c₁⊑c′ in
      let d₁⨟d⊑d′ = comp-pres-prec-bl d₁⊑d′ d⊑A′ in
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-addr x y) (⊑-ref c⨟c₁⊑c′ d₁⨟d⊑d′ c̅ₙ⊑c̅′) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-castr (⊑-addr x y) A⊑c′) c₁⊑A′ ⟩ =
  case ⟨ c₁⊑A′ , A⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-ref c₁⊑A′ d₁⊑A′ c̅₁⊑g′ , ⊑-ref A⊑c′ A⊑d′ g⊑c̅′ , ⊑-ref c⊑A′ d⊑A′ c̅⊑g′ , ir-ref 𝓋′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑g′ c̅⊑g′)) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
      let c⨟c₁⊑c′ = comp-pres-prec-lr (comp-pres-prec-ll c⊑A′ c₁⊑A′) A⊑c′ in
      let d₁⨟d⊑d′ = comp-pres-prec-rl A⊑d′ (comp-pres-prec-ll d₁⊑A′ d⊑A′) in
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-addr x y) (⊑-ref c⨟c₁⊑c′ d₁⨟d⊑d′ (comp-pres-⊑-rl g⊑c̅′ (⊑-left-contract c̅ₙ⊑id))) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castr (⊑-castl (⊑-addr x y) c₁⊑A′) A⊑c′ ⟩ =
  case ⟨ c₁⊑A′ , A⊑c′ , c⊑A′ , i′ ⟩ of λ where
  ⟨ ⊑-ref c₁⊑A′ d₁⊑A′ c̅₁⊑g′ , ⊑-ref A⊑c′ A⊑d′ g⊑c̅′ , ⊑-ref c⊑A′ d⊑A′ c̅⊑g′ , ir-ref 𝓋′ ⟩ →
    case catchupₗ _ _ 𝓋′ (comp-pres-⊑-bl (comp-pres-⊑-lr c̅₁⊑g′ g⊑c̅′) c̅⊑g′) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ →
      let c⨟c₁⊑c′ = comp-pres-prec-bl (comp-pres-prec-lr c⊑A′ A⊑c′) c₁⊑A′ in
      let d₁⨟d⊑d′ = comp-pres-prec-bl (comp-pres-prec-lr d₁⊑A′ A⊑d′) d⊑A′ in
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ _ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-cast (⊑-addr x y) (⊑-ref c⨟c₁⊑c′ d₁⨟d⊑d′ c̅ₙ⊑c̅ₙ′) ⟩
... | ⟨ ● , V-● , M↠● , ●⊑V′ ⟩ = contradiction ●⊑V′ (●⋤ _)
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-cast v′ i′) (⊑-castr M⊑V′ A⊑c′)
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′
... | ⟨ V , v , M↠V , V⊑V′ ⟩ = ⟨ V , v , M↠V , ⊑-castr V⊑V′ A⊑c′ ⟩
catchup V-● M⊑●  = contradiction M⊑● (_ ⋤●)
