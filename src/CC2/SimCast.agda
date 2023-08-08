module CC2.SimCast where

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
open import CoercionExpr.GG using (sim-mult)
open import CoercionExpr.CatchUp using (catchup)
open import CC2.Statics
open import CC2.CastReduction
open import CC2.Precision


sim-cast : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ B B′ V V′ W′} {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
  → Value V
  → Value V′
  → ⟨ c ⟩⊑⟨ c′ ⟩
  → V′ ⟨ c′ ⟩ —↠ W′
  → Value W′
    --------------------------------------
  → ∃[ W ] (Value W) × (V ⟨ c ⟩ —↠ W) × (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ W ⊑ W′ ⇐ B ⊑ B′)
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

-- sim-cast : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ B B′ M M′ N′}
--              {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
--   → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
--   → ⟨ c ⟩⊑⟨ c′ ⟩
--   → M′ ⟨ c′ ⟩ —→ N′
--   → ∃[ N ] (M ⟨ c ⟩ —↠ N) × (Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′)
-- sim-cast M⊑M′ c⊑c′ (cast x x₁ x₂) = {!!}
-- sim-cast M⊑M′ c⊑c′ (cast-blame x x₁) = {!!}
-- sim-cast M⊑M′ c⊑c′ cast-id = {!!}
-- sim-cast M⊑M′ c⊑c′ (cast-comp x x₁) = {!!}
