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



stamp-val!-prec : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {T T′ V V′} {ℓ ℓ′}
    → Γ ⊑* Γ′
    → Σ ⊑ₘ Σ′
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ T of ⋆ ⊑ T′ of ⋆
    → (v  : Value V )
    → (v′ : Value V′)
    → ℓ ≼ ℓ′
      ------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ stamp-val V v (T of ⋆) ℓ ⊑ stamp-val V′ v′ (T′ of ⋆) ℓ′
        ⇐ T of ⋆ ⊑ T′ of ⋆
-- if raw value on both sides
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ () (V-raw V-const) (V-raw V-const) ℓ≼ℓ′
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ () (V-raw V-addr) (V-raw V-addr) ℓ≼ℓ′
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ () (V-raw V-ƛ) (V-raw V-ƛ) ℓ≼ℓ′
-- raw value on one side wrapped value on the other
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr () A⊑c′) (V-raw V-addr) (V-cast V-addr (ir-ref {g = g} 𝓋′)) ℓ≼ℓ′
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr () A⊑c′) (V-raw V-ƛ) (V-cast V-ƛ (ir-fun {g = g} 𝓋′)) ℓ≼ℓ′
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castr () A⊑c′) (V-raw V-const) (V-cast V-const (ir-base {g = g} 𝓋′ x)) ℓ≼ℓ′
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl () c⊑A′) (V-cast V-addr (ir-ref {g = g} 𝓋)) (V-raw V-addr) ℓ≼ℓ′
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl () c⊑A′) (V-cast V-ƛ (ir-fun {g = g} 𝓋)) (V-raw V-ƛ) ℓ≼ℓ′
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ (⊑-castl () c⊑A′) (V-cast V-const (ir-base {g = g} 𝓋 x)) (V-raw V-const) ℓ≼ℓ′
-- wrapped values on both sides
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-cast v i) (V-cast v′ i′) ℓ≼ℓ′ =
  case cast-prec-inv V⊑V′ v v′ of λ where
  ⟨ W⊑W′ , c⊑c′ , refl , refl ⟩ → ⊑-cast W⊑W′ (stamp-ir!-prec c⊑c′ i i′ ℓ≼ℓ′)
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ ●⊑V′ V-● v′ = contradiction ●⊑V′ (●⋤ _)
stamp-val!-prec Γ⊑Γ′ Σ⊑Σ′ V⊑● v V-● = contradiction V⊑● (_ ⋤●)
