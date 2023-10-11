module Simulation.StampVal!LeftPrec where

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


stamp-val!-left-prec : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {A A′ V V′} {ℓ ℓ′}
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
  → (v  : Value V )
  → (v′ : Value V′)
  → ℓ ≼ ℓ′
    ------------------------------------------------------------------------------------
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ stamp-val! V v A ℓ ⊑ stamp-val V′ v′ A′ ℓ′
        ⇐ stamp A ⋆ ⊑ stamp A′ (l ℓ′)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw x) (V-raw x₁) l≼l = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-addr {n = n} {low} {ℓ̂} a b) (V-raw V-addr) (V-raw V-addr) l≼h =
  let A⊑A′ = ⊑-ty l⊑l (⊑ₘ→⊑ {n = n} {ℓ̂} Σ⊑Σ′ a b) in
  ⊑-cast (⊑-addr a b) (⊑-ref (prec-coerce-id A⊑A′) (prec-coerce-id A⊑A′) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-addr {n = n} {high} {ℓ̂} a b) (V-raw V-addr) (V-raw V-addr) l≼h =
  let A⊑A′ = ⊑-ty l⊑l (⊑ₘ→⊑ {n = n} {ℓ̂} Σ⊑Σ′ a b) in
  ⊑-castl (⊑-addr a b) (⊑-ref (prec-coerce-id-left A⊑A′) (prec-coerce-id-left A⊑A′) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-lam {ℓ = low} g⊑g′ A⊑A′ N⊑N′) (V-raw V-ƛ) (V-raw V-ƛ) l≼h =
  let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} (⊑*-∷ A⊑A′ Γ⊑Γ′) Σ⊑Σ′ N⊑N′ in
  ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun (⊑-id g⊑g′)
         (prec-coerce-id A⊑A′) (prec-coerce-id B⊑B′) !⊑↑)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-lam {ℓ = high} g⊑g′ A⊑A′ N⊑N′) (V-raw V-ƛ) (V-raw V-ƛ) l≼h =
  let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} (⊑*-∷ A⊑A′ Γ⊑Γ′) Σ⊑Σ′ N⊑N′ in
  ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun (⊑-id g⊑g′)
          (prec-coerce-id-left A⊑A′) (prec-coerce-id-left B⊑B′) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-const {ℓ = low}) (V-raw V-const) (V-raw V-const) l≼h =
  ⊑-cast ⊑-const (⊑-base !⊑↑)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-const {ℓ = high}) (V-raw V-const) (V-raw V-const) l≼h =
  ⊑-castl ⊑-const (⊑-base (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-addr a b) (V-raw V-addr) (V-raw V-addr) h≼h = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-lam g⊑g′ A⊑A′ N⊑N′) (V-raw V-ƛ) (V-raw V-ƛ) h≼h = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-const {ℓ = low}) (V-raw V-const) (V-raw V-const) h≼h =
  ⊑-cast ⊑-const (⊑-base ↑!⊑↑)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-const {ℓ = high}) (V-raw V-const) (V-raw V-const) h≼h =
  ⊑-castl ⊑-const (⊑-base (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr ⊑-const (⊑-base g⊑c̅′)) (V-raw V-const) (V-cast V-const (ir-base 𝓋′ _)) ℓ≼ℓ′ =
  ⊑-cast ⊑-const (⊑-base (stamp!ₗ-left-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr (⊑-addr a b) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′)) (V-raw V-addr) (V-cast V-addr (ir-ref 𝓋′)) ℓ≼ℓ′ =
  ⊑-cast (⊑-addr a b)
    (⊑-ref (prec-right-coerce-id A⊑c′) (prec-right-coerce-id A⊑d′)
           (stamp!ₗ-left-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′))
                               (V-raw V-ƛ) (V-cast V-ƛ (ir-fun 𝓋′)) ℓ≼ℓ′ =
  ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′)
    (⊑-fun (⊑-right-expand gc⊑d̅′) (prec-right-coerce-id A⊑c′) (prec-right-coerce-id B⊑d′)
           (stamp!ₗ-left-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl ⊑-const (⊑-base c̅⊑g′)) (V-cast V-const (ir-base {ℓ = ℓ₁} {g} 𝓋 _)) (V-raw V-const) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} with ℓ≼ℓ′ | ℓ₁
... | l≼l | low = ⊑-castl ⊑-const (⊑-base (stamp!ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼l))
... | l≼l | high = ⊑-castl ⊑-const (⊑-base (stamp!ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | l≼h | low = ⊑-cast ⊑-const (⊑-base (stamp!ₗ⊑↑ _ 𝓋))
... | l≼h | high = ⊑-castl ⊑-const (⊑-base (stamp!ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | h≼h | low = ⊑-cast ⊑-const (⊑-base (stamp!ₗ⊑↑ _ 𝓋))
... | h≼h | high = ⊑-castl ⊑-const (⊑-base (stamp!ₗ⊑ℓ _ c̅⊑g′ 𝓋 h≼h))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl (⊑-addr a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′)) (V-cast V-addr (ir-ref 𝓋)) (V-raw V-addr) ℓ≼ℓ′ = {!!}
  -- ⊑-cast (⊑-addr a b)
  --   (⊑-ref (prec-right-coerce-id A⊑c′) (prec-right-coerce-id A⊑d′)
  --          (stamp!ₗ-left-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′))
                               (V-cast V-ƛ (ir-fun 𝓋)) (V-raw V-ƛ) ℓ≼ℓ′ = {!!}
  -- ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′)
  --   (⊑-fun (⊑-right-expand gc⊑d̅′) (prec-right-coerce-id A⊑c′) (prec-right-coerce-id B⊑d′)
  --          (stamp!ₗ-left-prec id 𝓋′ (⊑-right-expand g⊑c̅′) ℓ≼ℓ′))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-cast v i) (V-cast v′ i′) ℓ≼ℓ′ = {!!}
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ ●⊑V′ V-● v′ = contradiction ●⊑V′ (●⋤ _)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑● v V-● = contradiction V⊑● (_ ⋤●)
