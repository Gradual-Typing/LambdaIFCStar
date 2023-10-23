module Simulation.SimCast where

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
open import CoercionExpr.CoercionExpr using (CVal⌿→)
open import CoercionExpr.Precision
open import CoercionExpr.CatchUpBack using (catchup-back)
open import CoercionExpr.GG using (sim-mult)
open import CoercionExpr.CatchUp using (catchup; catchup-to-id)
open import CC2.Statics
open import CC2.CastReduction
open import CC2.Reduction using (Value⌿→) renaming (cast to app-cast)
open import CC2.Precision


sim-cast : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ B B′ V V′ W′} {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
  → Value V
  → Value V′
  → ⟨ c ⟩⊑⟨ c′ ⟩
  → V′ ⟨ c′ ⟩ —↠ W′
  → Value W′
    --------------------------------------
  → ∃[ W ]    Value W  ×
       (V ⟨ c ⟩ —↠ W) ×
       (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ W ⊑ W′ ⇐ B ⊑ B′)
sim-cast ⊑-const (V-raw V-const) (V-raw V-const) (⊑-base c̅⊑c̅′) (_ ∎) (V-cast _ (ir-base 𝓋′ _)) =
  case catchup _ _ 𝓋′ c̅⊑c̅′ of λ where
  ⟨ d̅ , id , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-raw V-const ,
      _ —→⟨ cast-id ⟩ _ ∎ ,
      ⊑-castr ⊑-const (⊑-base (⊑-right-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , id , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-raw V-const ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) id ⟩ _ —→⟨ cast-id ⟩ _ ∎ ,
      ⊑-castr ⊑-const (⊑-base (⊑-right-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , inj 𝓋 , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (inj 𝓋) λ ()) , _ ∎ , ⊑-cast ⊑-const (⊑-base d̅⊑c̅′) ⟩
  ⟨ d̅ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (inj 𝓋) (λ ())) ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋) ⟩ _ ∎ ,
      ⊑-cast ⊑-const (⊑-base d̅⊑c̅′) ⟩
  ⟨ d̅ , up id , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (up id) λ ()) , _ ∎ , ⊑-cast ⊑-const (⊑-base d̅⊑c̅′) ⟩
  ⟨ d̅ , up id , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (up id) (λ ())) ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) (up id) ⟩ _ ∎ ,
      ⊑-cast ⊑-const (⊑-base d̅⊑c̅′) ⟩
sim-cast (⊑-addr x y) (V-raw V-addr) (V-raw V-addr) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) (_ ∎) (V-cast _ (ir-ref 𝓋′)) =
  case catchup _ _ 𝓋′ c̅⊑c̅′ of λ where
  ⟨ d̅ , 𝓋 , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-addr (ir-ref 𝓋) , _ ∎ , ⊑-cast (⊑-addr x y) (⊑-ref c⊑c′ d⊑d′ d̅⊑c̅′) ⟩
  ⟨ d̅ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-addr (ir-ref 𝓋) ,
      _ —→⟨ cast V-addr (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ _ ∎ ,
      ⊑-cast (⊑-addr x y) (⊑-ref c⊑c′ d⊑d′ d̅⊑c̅′) ⟩
sim-cast (⊑-lam x y z) (V-raw V-ƛ) (V-raw V-ƛ) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′) (_ ∎) (V-cast _ (ir-fun 𝓋′)) =
  case catchup _ _ 𝓋′ c̅⊑c̅′ of λ where
  ⟨ d̅ , 𝓋 , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-ƛ (ir-fun 𝓋) , _ ∎ , ⊑-cast (⊑-lam x y z) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ d̅⊑c̅′) ⟩
  ⟨ d̅ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-ƛ (ir-fun 𝓋) ,
      _ —→⟨ cast V-ƛ (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ _ ∎ ,
      ⊑-cast (⊑-lam x y z) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ d̅⊑c̅′) ⟩
sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-base c̅⊑c̅′) (_ —→⟨ cast _ c̅′→⁺c̅ₙ′ 𝓋′ ⟩ ↠W′) w′ =
  case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) of λ where
  ⟨ c̅ₙ , 𝓋 , _ ∎ₗ , c̅ₙ⊑c̅ₙ′ ⟩ → sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-base c̅ₙ⊑c̅ₙ′) ↠W′ w′
  ⟨ c̅ₙ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅ₙ′ ⟩ →
    let ⟨ W , w , ↠W , W⊑W′ ⟩ = sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-base c̅ₙ⊑c̅ₙ′) ↠W′ w′ in
    ⟨ W , w , _ —→⟨ cast v (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ ↠W , W⊑W′ ⟩
sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) (_ —→⟨ cast _ c̅′→⁺c̅ₙ′ 𝓋′ ⟩ ↠W′) w′ =
  case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) of λ where
  ⟨ c̅ₙ , 𝓋 , _ ∎ₗ , c̅ₙ⊑c̅ₙ′ ⟩ → sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-ref c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ↠W′ w′
  ⟨ c̅ₙ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅ₙ′ ⟩ →
    let ⟨ W , w , ↠W , W⊑W′ ⟩ = sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-ref c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ↠W′ w′ in
    ⟨ W , w , _ —→⟨ cast v (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ ↠W , W⊑W′ ⟩
sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′) (_ —→⟨ cast _ c̅′→⁺c̅ₙ′ 𝓋′ ⟩ ↠W′) w′ =
  case sim-mult c̅⊑c̅′ 𝓋′ (→⁺-impl-↠ c̅′→⁺c̅ₙ′) of λ where
  ⟨ c̅ₙ , 𝓋 , _ ∎ₗ , c̅ₙ⊑c̅ₙ′ ⟩ → sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ↠W′ w′
  ⟨ c̅ₙ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , c̅ₙ⊑c̅ₙ′ ⟩ →
    let ⟨ W , w , ↠W , W⊑W′ ⟩ = sim-cast V⊑V′ (V-raw v) (V-raw v′) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅ₙ⊑c̅ₙ′) ↠W′ w′ in
    ⟨ W , w , _ —→⟨ cast v (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ ↠W , W⊑W′ ⟩
sim-cast V⊑V′ (V-raw v) (V-raw v′) c⊑c′ (_ —→⟨ cast-blame x x₁ ⟩ _ ∎) (V-raw ())
sim-cast ⊑-const (V-raw V-const) (V-raw V-const) (⊑-base c̅⊑id) (_ —→⟨ cast-id ⟩ _ ∎) (V-raw V-const) =
  case catchup _ _ id c̅⊑id of λ where
  ⟨ d̅ , id , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-raw V-const ,
      _ —→⟨ cast-id ⟩ _ ∎ ,
      ⊑-const ⟩
  ⟨ d̅ , id , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-raw V-const ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) id ⟩ _ —→⟨ cast-id ⟩ _ ∎ ,
      ⊑-const ⟩
  ⟨ d̅ , inj 𝓋 , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (inj 𝓋) λ ()) , _ ∎ ,
      ⊑-castl ⊑-const (⊑-base (⊑-left-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (inj 𝓋) (λ ())) ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋) ⟩ _ ∎ ,
      ⊑-castl ⊑-const (⊑-base (⊑-left-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , up id , _ , ⊑-castl _ l⊑l () ⟩
sim-cast V⊑V′ (V-raw _) (V-cast x₁ x₂) c⊑c′ (_ ∎) (V-cast () _)
sim-cast {c = c} {c′} (⊑-castr V⊑V′ A⊑d′) (V-raw v) (V-cast {c = d′} v′ i′) c⊑c′ (_ —→⟨ cast-comp _ _ ⟩ r*) w′ =
  let c⊑d′⨟c′ = comp-pres-prec-rb A⊑d′ c⊑c′ in
  sim-cast V⊑V′ (V-raw v) (V-raw v′) c⊑d′⨟c′ r* w′
sim-cast {c = c} {c′} (⊑-castl V⊑V′ d⊑A′) (V-cast {V = V} {c = d} v i) (V-raw v′) c⊑c′ r* w′ =
  let d⨟c⊑c′ : ⟨ d ⨟ c ⟩⊑⟨ c′ ⟩
      d⨟c⊑c′ = comp-pres-prec-lb d⊑A′ c⊑c′ in
  let ⟨ W , w , ↠W , W⊑W′ ⟩ = sim-cast V⊑V′ (V-raw v) (V-raw v′) d⨟c⊑c′ r* w′ in
  ⟨ W , w , _ —→⟨ cast-comp v i ⟩ ↠W , W⊑W′ ⟩
sim-cast V⟨d⟩⊑V′⟨d′⟩ (V-cast v i) (V-cast v′ i′) c⊑c′ (_ ∎) (V-cast () _)
sim-cast V⟨d⟩⊑V′⟨d′⟩ (V-cast {V = V} {c} v i) (V-cast {V = V′} {c′} v′ i′) c⊑c′ (_ —→⟨ cast-comp _ _ ⟩ r*) w′
  with cast-prec-inv V⟨d⟩⊑V′⟨d′⟩ v v′
... | ⟨ V⊑V′ , d⊑d′ , refl , refl ⟩ =
  let d⨟c⊑d′⨟c′ = comp-pres-prec d⊑d′ c⊑c′ in
  let ⟨ W , w , ↠W , W⊑W′ ⟩ = sim-cast V⊑V′ (V-raw v) (V-raw v′) d⨟c⊑d′⨟c′ r* w′ in
  ⟨ W , w , _ —→⟨ cast-comp v i ⟩ ↠W , W⊑W′ ⟩
sim-cast V⊑V′ v V-●  c⊑c′ ↠W′ w′ = contradiction V⊑V′ (_ ⋤●)
sim-cast V⊑V′ V-● v′ c⊑c′ ↠W′ w′ = contradiction V⊑V′ (●⋤ _)


sim-cast-left : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ B V V′} {c : Cast A ⇒ B}
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
  → Value V
  → Value V′
  → ⟨ c ⟩⊑ A′
    -------------------------------------------------------------------
  → ∃[ W ]    Value W  ×
       (V ⟨ c ⟩ —↠ W) ×
       (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ W ⊑ V′ ⇐ B ⊑ A′)
sim-cast-left ⊑-const (V-raw V-const) (V-raw V-const) (⊑-base c̅⊑g′) =
  case catchup-to-id _ (⊑-left-expand c̅⊑g′) of λ where
  ⟨ d̅ , id , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-raw V-const ,
      _ —→⟨ cast-id ⟩ _ ∎ , ⊑-const ⟩
  ⟨ d̅ , id , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-raw V-const ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) id ⟩ _ —→⟨ cast-id ⟩ _ ∎ , ⊑-const ⟩
  ⟨ d̅ , inj 𝓋 , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (inj 𝓋) λ ()) , _ ∎ ,
      ⊑-castl ⊑-const (⊑-base (⊑-left-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , inj 𝓋 , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (inj 𝓋) (λ ())) ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) (inj 𝓋) ⟩ _ ∎ ,
      ⊑-castl ⊑-const (⊑-base (⊑-left-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , up id , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (up id) λ ()) , _ ∎ ,
      ⊑-castl ⊑-const (⊑-base (⊑-left-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , up id , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-const (ir-base (up id) (λ ())) ,
      _ —→⟨ cast V-const (_ —→ₗ⟨ r ⟩ r*) (up id) ⟩ _ ∎ ,
      ⊑-castl ⊑-const (⊑-base (⊑-left-contract d̅⊑c̅′)) ⟩
sim-cast-left (⊑-addr x y) (V-raw V-addr) (V-raw V-addr) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  case catchup-to-id _ (⊑-left-expand c̅⊑g′) of λ where
  ⟨ d̅ , 𝓋 , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-addr (ir-ref 𝓋) , _ ∎ ,
      ⊑-castl (⊑-addr x y) (⊑-ref c⊑A′ d⊑A′ (⊑-left-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-addr (ir-ref 𝓋) ,
      _ —→⟨ cast V-addr (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ _ ∎ ,
      ⊑-castl (⊑-addr x y) (⊑-ref c⊑A′ d⊑A′ (⊑-left-contract d̅⊑c̅′)) ⟩
sim-cast-left (⊑-lam g⊑g′ A⊑A′ N⊑N′) (V-raw V-ƛ) (V-raw V-ƛ) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) =
  case catchup-to-id _ (⊑-left-expand c̅⊑g′) of λ where
  ⟨ d̅ , 𝓋 , _ ∎ₗ , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-ƛ (ir-fun 𝓋) , _ ∎ ,
      ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (⊑-left-contract d̅⊑c̅′)) ⟩
  ⟨ d̅ , 𝓋 , _ —→ₗ⟨ r ⟩ r* , d̅⊑c̅′ ⟩ →
    ⟨ _ , V-cast V-ƛ (ir-fun 𝓋) ,
      _ —→⟨ cast V-ƛ (_ —→ₗ⟨ r ⟩ r*) 𝓋 ⟩ _ ∎ ,
      ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (⊑-left-contract d̅⊑c̅′)) ⟩
sim-cast-left (⊑-castr V⊑V′ A⊑c′) (V-raw v) (V-cast v′ i′) c⊑A′ =
  let c⊑c′ = comp-pres-prec-rl A⊑c′ c⊑A′ in
  sim-cast V⊑V′ (V-raw v) (V-raw v′) c⊑c′ (_ ∎) (V-cast v′ i′)
sim-cast-left (⊑-castl V⊑V′ c⊑A′) (V-cast v i) (V-raw v′) d⊑A′ =
  let c⨟d⊑A′ = comp-pres-prec-ll c⊑A′ d⊑A′ in
  let ⟨ W , w , ↠W , W⊑W′ ⟩ = sim-cast-left V⊑V′ (V-raw v) (V-raw v′) c⨟d⊑A′ in
  ⟨ W , w , _ —→⟨ cast-comp v i ⟩ ↠W , W⊑W′ ⟩
sim-cast-left V⟨c⟩⊑V′⟨c′⟩ (V-cast {V = V} {c} v i) (V-cast {V = V′} {c′} v′ i′) d⊑A′
  with cast-prec-inv V⟨c⟩⊑V′⟨c′⟩ v v′
... | ⟨ V⊑V′ , c⊑c′ , refl , refl ⟩ =
  let c⨟d⊑c′ = comp-pres-prec-bl c⊑c′ d⊑A′ in
  let ⟨ W , w , ↠W , W⊑W′ ⟩ = sim-cast V⊑V′ (V-raw v) (V-raw v′) c⨟d⊑c′ (_ ∎) (V-cast v′ i′) in
  ⟨ W , w , _ —→⟨ cast-comp v i ⟩ ↠W , W⊑W′ ⟩
sim-cast-left V⊑V′ V-● v′ c⊑A′ = contradiction V⊑V′ (●⋤ _)
sim-cast-left V⊑V′ v V-● c⊑A′ = contradiction V⊑V′ (_ ⋤●)


{- A better `sim-cast-right` should look like `sim-cast-left`. In that case,
   we need to prove that cast reduction is deterministic, so I guess this
   version is good enough for now. -}
sim-cast-right : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ B′ V V′ W′} {c′ : Cast A′ ⇒ B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
    → Value V
    → Value V′
    → A ⊑⟨ c′ ⟩
    → V′ ⟨ c′ ⟩ —↠ W′
    → Value W′
      -------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ W′ ⇐ A ⊑ B′
sim-cast-right V⊑V′ v v′ A⊑c′ (_ ∎) w′ = ⊑-castr V⊑V′ A⊑c′
sim-cast-right V⊑V′ v v′ (⊑-base g⊑c̅′) (_ —→⟨ cast vᵣ c̅′→⁺c̅ₙ 𝓋 ⟩ r*) w′ =
  let g⊑c̅ₙ = pres-prec-right-mult g⊑c̅′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) in
  sim-cast-right V⊑V′ v v′ (⊑-base g⊑c̅ₙ) r* w′
sim-cast-right V⊑V′ v v′ (⊑-ref x y g⊑c̅′) (_ —→⟨ cast vᵣ c̅′→⁺c̅ₙ 𝓋 ⟩ r*) w′ =
  let g⊑c̅ₙ = pres-prec-right-mult g⊑c̅′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) in
  sim-cast-right V⊑V′ v v′ (⊑-ref x y g⊑c̅ₙ) r* w′
sim-cast-right V⊑V′ v v′ (⊑-fun x y z g⊑c̅′) (_ —→⟨ cast vᵣ c̅′→⁺c̅ₙ 𝓋 ⟩ r*) w′ =
  let g⊑c̅ₙ = pres-prec-right-mult g⊑c̅′ (→⁺-impl-↠ c̅′→⁺c̅ₙ) in
  sim-cast-right V⊑V′ v v′ (⊑-fun x y z g⊑c̅ₙ) r* w′
sim-cast-right V⊑V′ v v′ A⊑c′ (_ —→⟨ cast-blame x x₁ ⟩ _ ∎) (V-raw ())
sim-cast-right V⊑V′ v v′ A⊑c′ (_ —→⟨ cast-id ⟩ _ ∎) (V-raw V-const) = V⊑V′
-- the two cases below require some thinking
sim-cast-right (⊑-cast V⊑V′ c⊑c′) (V-cast vᵣ i) (V-cast vᵣ′ i′) A⊑c′₁ (_ —→⟨ cast-comp vᵣ′† i′† ⟩ r*) w′
  with sim-cast V⊑V′ (V-raw vᵣ) (V-raw vᵣ′) (comp-pres-prec-br c⊑c′ A⊑c′₁) r* w′
... | ⟨ W , w , _ ∎ , prec ⟩ = prec
... | ⟨ W , w , _ —→⟨ r ⟩ _ , prec ⟩ =
  contradiction (app-cast (V-raw vᵣ) r) (Value⌿→ {μ = ∅} {PC = l low} (V-cast vᵣ i))
sim-cast-right (⊑-castl (⊑-castr V⊑V′ A⊑c′) c⊑A′) (V-cast vᵣ i) v′ B⊑c₁′ (_ —→⟨ cast-comp vᵣ′ i′ ⟩ r*) w′
  with sim-cast V⊑V′ (V-raw vᵣ) (V-raw vᵣ′) (comp-pres-prec-br (comp-pres-prec-rl A⊑c′ c⊑A′) B⊑c₁′) r* w′
... | ⟨ W , w , _ ∎ , prec ⟩ = prec
... | ⟨ W , w , _ —→⟨ r ⟩ _ , prec ⟩ =
  contradiction (app-cast (V-raw vᵣ) r) (Value⌿→ {μ = ∅} {PC = l low} (V-cast vᵣ i))
sim-cast-right (⊑-castr V⊑V′ A⊑c′₁) v v′ A⊑c′ (_ —→⟨ cast-comp vᵣ i ⟩ r*) w′ =
  sim-cast-right V⊑V′ v (V-raw vᵣ) (comp-pres-prec-rr A⊑c′₁ A⊑c′) r* w′
