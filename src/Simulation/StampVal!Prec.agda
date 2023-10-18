module Simulation.StampVal!Prec where

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
open import CoercionExpr.Precision
open import CoercionExpr.Stamping
open import Memory.HeapContext
open import CC2.Statics
open import CC2.Precision
open import CC2.Stamping public



stamp-val!-prec : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {A A′ V V′} {ℓ ℓ′}
    → Γ ⊑* Γ′
    → Σ ⊑ₘ Σ′
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
    → (v  : Value V )
    → (v′ : Value V′)
    → ℓ ≼ ℓ′
      ------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ stamp-val! V v A ℓ ⊑ stamp-val! V′ v′ A′ ℓ′
        ⇐ stamp A ⋆ ⊑ stamp A′ ⋆
-- if raw value on both sides
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ ⊑-const (V-raw V-const) (V-raw V-const) ℓ≼ℓ′ =
  ⊑-cast ⊑-const (⊑-base (stamp!ₗ-prec id id (⊑-id l⊑l) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-addr {n = n} {ℓ} {ℓ̂} a b) (V-raw V-addr) (V-raw V-addr) ℓ≼ℓ′ =
  let A⊑A′ = ⊑-ty l⊑l (⊑ₘ→⊑ {n = n} {ℓ̂} Σ⊑Σ′ a b) in
  ⊑-cast (⊑-addr a b) (⊑-ref (prec-coerce-id A⊑A′) (prec-coerce-id A⊑A′) (stamp!ₗ-prec id id (⊑-id l⊑l) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-lam g⊑g′ A⊑A′ N⊑N′) (V-raw V-ƛ) (V-raw V-ƛ) ℓ≼ℓ′ =
  let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} (⊑*-∷ A⊑A′ Γ⊑Γ′) Σ⊑Σ′ N⊑N′ in
  ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun (⊑-id g⊑g′) (prec-coerce-id A⊑A′) (prec-coerce-id B⊑B′) (stamp!ₗ-prec id id (⊑-id l⊑l) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr (⊑-addr a b) A⊑c′) (V-raw V-addr) (V-cast V-addr (ir-ref {g = g} 𝓋′)) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} =
  case A⊑c′ of λ where
  (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) →
    ⊑-cast (⊑-addr a b) (⊑-ref (prec-right-coerce-id A⊑c′) (prec-right-coerce-id A⊑d′)
      (stamp!ₗ-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr (⊑-lam g⊑g′ A⊑A′ N⊑N′) A⊑c′) (V-raw V-ƛ) (V-cast V-ƛ (ir-fun {g = g} 𝓋′)) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} =
  case A⊑c′ of λ where
  (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′) →
    ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′)
           (⊑-fun (⊑-right-expand gc⊑d̅′) (prec-right-coerce-id A⊑c′) (prec-right-coerce-id B⊑d′)
                  (stamp!ₗ-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr ⊑-const A⊑c′) (V-raw V-const) (V-cast V-const (ir-base {g = g} 𝓋′ x)) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} =
  case A⊑c′ of λ where
  (⊑-base g⊑c̅′) →
    ⊑-cast ⊑-const (⊑-base (stamp!ₗ-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl (⊑-addr a b) c⊑A′) (V-cast V-addr (ir-ref {g = g} 𝓋)) (V-raw V-addr) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} =
  case c⊑A′ of λ where
  (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) →
    ⊑-cast (⊑-addr a b) (⊑-ref (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑A′)
      (stamp!ₗ-prec 𝓋 id (⊑-left-expand c̅⊑g′) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) c⊑A′) (V-cast V-ƛ (ir-fun {g = g} 𝓋)) (V-raw V-ƛ) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} =
  case c⊑A′ of λ where
  (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) →
    ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′)
           (⊑-fun (⊑-left-expand d̅⊑gc′) (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑B′)
                  (stamp!ₗ-prec 𝓋 id (⊑-left-expand c̅⊑g′) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl ⊑-const c⊑A′) (V-cast V-const (ir-base {g = g} 𝓋′ x)) (V-raw V-const) ℓ≼ℓ′ = {!!}
  -- rewrite g⋎̃⋆≡⋆ {g} =
  -- case A⊑c′ of λ where
  -- (⊑-base g⊑c̅′) →
  --   ⊑-cast ⊑-const (⊑-base (stamp!ₗ-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-cast v i) (V-cast v′ i′) ℓ≼ℓ′ = {!!}
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ ●⊑V′ V-● v′ = contradiction ●⊑V′ (●⋤ _)
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑● v V-● = contradiction V⊑● (_ ⋤●)
