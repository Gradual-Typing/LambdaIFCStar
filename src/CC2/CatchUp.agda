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
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
    -------------------------------------------------------------------
  → ∃[ V ] (Value V) ×
       (M ∣ μ ∣ PC —↠ V ∣ μ) ×
       (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′)
catchup (V-raw x) ⊑-const Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup (V-raw x) (⊑-addr x₁ x₂) Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup (V-raw x) (⊑-lam x₁ x₂ x₃) Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup {gc = gc} {gc′} {ℓv} {ℓv′} {μ = μ} {PC} (V-raw v′) (⊑-castl {c = c} M⊑V′ c⊑A′) Γ⊑Γ′ Σ⊑Σ′
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′ Γ⊑Γ′ Σ⊑Σ′ | v′ | c
... | ⟨ V , V-raw V-const , M↠V , ⊑-const ⟩ | V-const | cast (id ι) c̅ =
  {- proof could be simplified if we use `catchupₗ` here instead of `cexpr-sn` -}
  case cexpr-sn c̅ of λ where
  ⟨ _ , _ ∎ₗ , success id ⟩ →
    ⟨ V , V-raw V-const ,
      trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                 (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                  _ ∣ _ ∣ _ ∎) ,
      ⊑-const ⟩
  ⟨ _ , _ —→ₗ⟨ r ⟩ r* , success id ⟩ →
    ⟨ V , V-raw V-const ,
      trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                 (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) CVal.id) ⟩
                  _ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) cast-id ⟩
                  _ ∣ _ ∣ _ ∎) ,
      ⊑-const ⟩
  ⟨ _ , _ ∎ₗ , success (inj id) ⟩ →
    ⟨ V ⟨ cast (Castᵣ_⇒_.id ι) (_ ⨾ CC2.Statics._! _) ⟩ ,
      V-cast V-const (ir-base (inj CVal.id) (λ ())) ,
      plug-cong (□⟨ _ ⟩) M↠V ,
      ⊑-castl ⊑-const (⊑-base (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)) ⟩
  ⟨ _ , _ —→ₗ⟨ r ⟩ r* , success (inj id) ⟩ →
    ⟨ V ⟨ cast (Castᵣ_⇒_.id ι) (_ ⨾ CC2.Statics._! _) ⟩ ,
      V-cast V-const (ir-base (inj CVal.id) (λ ())) ,
      trans-mult (plug-cong (□⟨ _ ⟩) M↠V)
                 (_ ∣ _ ∣ _ —→⟨ cast (V-raw V-const) (cast V-const (_ —→ₗ⟨ r ⟩ r*) (inj CVal.id)) ⟩
                  _ ∣ _ ∣ _ ∎) ,
      ⊑-castl ⊑-const (⊑-base (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)) ⟩
  ⟨ _ , c̅↠d̅ , success (inj (up id)) ⟩ →
    case c⊑A′ of λ where         {- impossible -}
    (⊑-base c̅⊑low) →
      case pres-prec-left-mult c̅⊑low c̅↠d̅ of λ where
      (⊑-cast _ () _)
  ⟨ _ , c̅↠↑ , success (up id) ⟩ →
    case c⊑A′ of λ where         {- impossible -}
    (⊑-base c̅⊑low) →
      case pres-prec-left-mult c̅⊑low c̅↠↑ of λ where
      (⊑-cast _ _ ())
  ⟨ ⊥ _ _ p , c̅↠⊥ , fail ⟩ →
    case c⊑A′ of λ where         {- impossible -}
    (⊑-base c̅⊑g′) →
      case pres-prec-left-mult c̅⊑g′ c̅↠⊥ of λ where ()
... | ⟨ V , V-raw V-ƛ , M↠V , ⊑-lam g⊑g′ A⊑A′ N⊑N′ ⟩ | V-ƛ | cast (fun d̅ c d) c̅ = {!!}
... | ⟨ V , V-raw V-addr , M↠V , ⊑-addr _ _ ⟩ | V-addr | cast (ref c d) c̅ = {!!}
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
catchup (V-cast x x₁) M⊑V′ Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup V-● M⊑● Γ⊑Γ′ Σ⊑Σ′ = contradiction M⊑● (_ ⋤●)
