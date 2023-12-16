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


stamp-val!-left-prec : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {T A′ V V′} {ℓ ℓ′}
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ T of ⋆ ⊑ A′
  → (v  : Value V )
  → (v′ : Value V′)
  → ℓ ≼ ℓ′
    ------------------------------------------------------------------------------------
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ stamp-val V v (T of ⋆) ℓ ⊑ stamp-val V′ v′ A′ ℓ′
        ⇐ T of ⋆ ⊑ stamp A′ (l ℓ′)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ () (V-raw V-addr) (V-raw V-addr) _
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ () (V-raw V-const) (V-raw V-const) _
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ () (V-raw V-ƛ) (V-raw V-ƛ) _
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr () _) (V-raw V-const) (V-cast V-const (ir-base 𝓋′ _)) _
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr () (⊑-ref A⊑c′ A⊑d′ g⊑c̅′)) (V-raw V-addr) (V-cast V-addr (ir-ref 𝓋′)) _
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr () (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′)) (V-raw V-ƛ) (V-cast V-ƛ (ir-fun 𝓋′)) _
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl ⊑-const (⊑-base c̅⊑g′))
                               (V-cast V-const (ir-base {ℓ = ℓ₁} {g} 𝓋 _)) (V-raw V-const) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} with ℓ≼ℓ′ | ℓ₁
... | l≼l | low = ⊑-castl ⊑-const (⊑-base (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼l))
... | l≼l | high = ⊑-castl ⊑-const (⊑-base (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | l≼h | low = ⊑-cast ⊑-const (⊑-base (stamp⋆ₗ⊑↑ _ 𝓋))
... | l≼h | high = ⊑-castl ⊑-const (⊑-base (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | h≼h | low = ⊑-cast ⊑-const (⊑-base (stamp⋆ₗ⊑↑ {high} _ 𝓋))
... | h≼h | high = ⊑-castl ⊑-const (⊑-base (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 h≼h))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl (⊑-addr a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′))
                               (V-cast V-addr (ir-ref {ℓ = ℓ₁} {g} 𝓋)) (V-raw V-addr) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} with ℓ≼ℓ′ | ℓ₁
... | l≼l | low = ⊑-castl (⊑-addr a b) (⊑-ref c⊑A′ d⊑A′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼l))
... | l≼l | high = ⊑-castl (⊑-addr a b) (⊑-ref c⊑A′ d⊑A′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | l≼h | low = ⊑-cast (⊑-addr a b) (⊑-ref (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑A′) (stamp⋆ₗ⊑↑ _ 𝓋))
... | l≼h | high = ⊑-castl (⊑-addr a b) (⊑-ref c⊑A′ d⊑A′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | h≼h | low = ⊑-cast (⊑-addr a b) (⊑-ref  (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑A′) (stamp⋆ₗ⊑↑ {high} _ 𝓋))
... | h≼h | high = ⊑-castl (⊑-addr a b) (⊑-ref c⊑A′ d⊑A′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 h≼h))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′))
                               (V-cast V-ƛ (ir-fun {ℓ = ℓ₁} {g} 𝓋)) (V-raw V-ƛ) ℓ≼ℓ′
  rewrite g⋎̃⋆≡⋆ {g} with ℓ≼ℓ′ | ℓ₁
... | l≼l | low = ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼l))
... | l≼l | high = ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | l≼h | low = ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′)
  (⊑-fun (⊑-left-expand d̅⊑gc′) (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑B′) (stamp⋆ₗ⊑↑ _ 𝓋))
... | l≼h | high =  ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 l≼h))
... | h≼h | low = ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′)
  (⊑-fun (⊑-left-expand d̅⊑gc′) (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑B′) (stamp⋆ₗ⊑↑ {high} _ 𝓋))
... | h≼h | high = ⊑-castl (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ (stamp⋆ₗ⊑ℓ _ c̅⊑g′ 𝓋 h≼h))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-cast v i) (V-cast v′ i′) ℓ≼ℓ′
  with cast-prec-inv V⊑V′ v v′ | i | i′
... | ⟨ ⊑-const , ⊑-base c̅⊑c̅′ , refl , refl ⟩ | ir-base {g = g} 𝓋 _ | ir-base 𝓋′ _
  rewrite g⋎̃⋆≡⋆ {g} = ⊑-cast ⊑-const (⊑-base (stamp⋆ₗ-left-prec 𝓋 𝓋′ c̅⊑c̅′ ℓ≼ℓ′))
... | ⟨ ⊑-addr a b , ⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′ , refl , refl ⟩ | ir-ref {g = g} 𝓋 | ir-ref 𝓋′
  rewrite g⋎̃⋆≡⋆ {g} = ⊑-cast (⊑-addr a b) (⊑-ref c⊑c′ d⊑d′ (stamp⋆ₗ-left-prec 𝓋 𝓋′ c̅⊑c̅′ ℓ≼ℓ′))
... | ⟨ ⊑-lam g⊑g′ A⊑A′ N⊑N′ , ⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′ , refl , refl ⟩ | ir-fun {g = g} 𝓋 | ir-fun 𝓋′
  rewrite g⋎̃⋆≡⋆ {g} = ⊑-cast (⊑-lam g⊑g′ A⊑A′ N⊑N′) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ (stamp⋆ₗ-left-prec 𝓋 𝓋′ c̅⊑c̅′ ℓ≼ℓ′))
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ ●⊑V′ V-● v′ = contradiction ●⊑V′ (●⋤ _)
stamp-val!-left-prec Γ⊑Γ′ Σ⊑Σ′ V⊑● v V-● = contradiction V⊑● (_ ⋤●)
