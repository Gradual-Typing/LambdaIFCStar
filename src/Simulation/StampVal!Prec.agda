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
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr (⊑-addr a b) _) (V-raw V-addr) (V-cast V-addr i′) ℓ≼ℓ′ =
  {!!}
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw V-ƛ) (V-cast v′ i′) ℓ≼ℓ′ = {!!}
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw V-const) (V-cast v′ i′) ℓ≼ℓ′ = {!!}
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-cast v i) (V-raw v′) ℓ≼ℓ′ = {!!}
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-cast v i) (V-cast v′ i′) ℓ≼ℓ′ = {!!}
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ ●⊑V′ V-● v′ = contradiction ●⊑V′ (●⋤ _)
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑● v V-● = contradiction V⊑● (_ ⋤●)
