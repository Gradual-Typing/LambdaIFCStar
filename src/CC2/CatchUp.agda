module CC2.CatchUp where

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
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′  | v′ | c
... | ⟨ V , V-raw V-const , M↠V , ⊑-const ⟩ | V-const | cast (id ι) c̅ =
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
... | ⟨ V , V-raw V-ƛ , M↠V , ⊑-lam g⊑g′ A⊑A′ N⊑N′ ⟩ | V-ƛ | cast (fun d̅ c d) c̅ =
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
... | ⟨ V , V-raw V-addr , M↠V , ⊑-addr x y ⟩ | V-addr | cast (ref c d) c̅ =
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
... | ⟨ V ⟨ cast _ d̅ ⟩ , V-cast v i , M↠V , ⊑-castl ⊑-const d⊑A′ ⟩ | V-const | cast (id ι) c̅ =
  case ⟨ d⊑A′ , c⊑A′ ⟩ of λ where
  ⟨ ⊑-base d̅⊑g′ , ⊑-base c̅⊑g′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll d̅⊑g′ c̅⊑g′)) of λ where
    ⟨ _ , id , d̅⨟c̅↠id , id⊑id ⟩ →
      ⟨ _ , V-raw v ,
        trans-mult (plug-cong □⟨ cast (id ι) c̅ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠id id) id) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) cast-id ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-const ⟩
    ⟨ _ , inj 𝓋 , d̅⨟c̅↠! , !⊑id ⟩ →
      ⟨ _ , V-cast v (ir-base {ι = ι} (inj 𝓋) (λ ())) ,
        trans-mult (plug-cong □⟨ cast (id ι) c̅ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠! (inj 𝓋)) (inj 𝓋)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl ⊑-const (⊑-base (⊑-left-contract !⊑id)) ⟩
    ⟨ _ , up id , d̅⨟c̅↠↑ , ↑⊑id ⟩ →
      ⟨ _ , V-cast v (ir-base {ι = ι} (up id) (λ ())) ,
        trans-mult (plug-cong □⟨ cast (id ι) c̅ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ d̅⨟c̅↠↑ (up id)) (up id)) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl ⊑-const (⊑-base (⊑-left-contract ↑⊑id)) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) d⊑A′ ⟩ | V-ƛ | cast (fun d̅ c d) c̅ =
  case ⟨ d⊑A′ , c⊑A′ ⟩ of λ where
  ⟨ ⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑g′ c̅⊑g′)) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
      let d̅⨟d̅₁⊑gc′ = comp-pres-⊑-ll d̅⊑gc′ d̅₁⊑gc′ in
      let c⨟c₁⊑A′ = comp-pres-prec-ll c⊑A′ c₁⊑A′ in
      let d₁⨟d⊑B′ = comp-pres-prec-ll d₁⊑B′ d⊑B′ in
      ⟨ _ , V-cast v (ir-fun 𝓋) ,
        trans-mult (plug-cong □⟨ cast (fun d̅ c d) c̅ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′)
                (⊑-fun d̅⨟d̅₁⊑gc′ c⨟c₁⊑A′ d₁⨟d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ V , V-cast v i , M↠V , ⊑-castl (⊑-addr x y) d⊑A′ ⟩ | V-addr | cast (ref c d) c̅ =
  case ⟨ d⊑A′ , c⊑A′ ⟩ of λ where
  ⟨ ⊑-ref c₁⊑A′ d₁⊑B′ c̅₁⊑g′ , ⊑-ref c⊑A′ d⊑B′ c̅⊑g′ ⟩ →
    case catchupₗ _ _ CVal.id (⊑-left-expand (comp-pres-⊑-ll c̅₁⊑g′ c̅⊑g′)) of λ where
    ⟨ c̅ₙ , 𝓋 , c̅₁⨟c̅↠c̅ₙ , c̅ₙ⊑id ⟩ →
      let c⨟c₁⊑A′ = comp-pres-prec-ll c⊑A′ c₁⊑A′ in
      let d₁⨟d⊑B′ = comp-pres-prec-ll d₁⊑B′ d⊑B′ in
      ⟨ _ , V-cast v (ir-ref 𝓋) ,
        trans-mult (plug-cong □⟨ cast (ref c d) c̅ ⟩ M↠V)
                   (_ ∣ _ ∣ _ —→⟨ cast (V-cast v i) (cast-comp v i) ⟩
                    _ ∣ _ ∣ _ —→⟨ cast (V-raw v) (cast v (comp-→⁺ c̅₁⨟c̅↠c̅ₙ 𝓋) 𝓋) ⟩
                    _ ∣ _ ∣ _ ∎) ,
        ⊑-castl (⊑-addr x y)
                (⊑-ref c⨟c₁⊑A′ d₁⨟d⊑B′ (⊑-left-contract c̅ₙ⊑id)) ⟩
... | ⟨ ● , V-● , M↠● , ●⊑V′ ⟩ | v′ | c = contradiction ●⊑V′ (●⋤ _)
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-cast v′ i′) (⊑-cast M⊑M′ c⊑c′) = {!!}
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-cast v′ i′) (⊑-castl M⊑M′ c⊑A′) = {!!}
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-cast v′ i′) (⊑-castr M⊑V′ A⊑c′)
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′
... | ⟨ V , v , M↠V , V⊑V′ ⟩ = ⟨ V , v , M↠V , ⊑-castr V⊑V′ A⊑c′ ⟩
catchup V-● M⊑●  = contradiction M⊑● (_ ⋤●)
