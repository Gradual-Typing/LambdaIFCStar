module CC2.StampValPrec where

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
open import Memory.HeapContext
open import CC2.Statics
open import CC2.Precision


stamp-val-prec : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {A A′ V V′} {ℓ}
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ V ⊑ V′ ⇐ A ⊑ A′
  → (v  : Value V )
  → (v′ : Value V′)
    ------------------------------------------------------------------------------------
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ stamp-val V v A ℓ ⊑ stamp-val V′ v′ A′ ℓ
        ⇐ stamp A (l ℓ) ⊑ stamp A′ (l ℓ)
stamp-val-prec {A = T of ⋆} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw v) (V-raw v′) =
  case ⟨ v , cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ V⊑V′ ⟩ of λ where
  ⟨ V-const , () , _ ⟩
  ⟨ V-addr , () , _ ⟩
  ⟨ V-ƛ , () , _ ⟩
stamp-val-prec {A = ` _ of l high} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ ⊑-const (V-raw x) (V-raw x₁) = ⊑-const
stamp-val-prec {A = Ref (_ of l _) of l high} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-addr a b) (V-raw _) (V-raw _) = ⊑-addr a b
stamp-val-prec {A = ⟦ _ ⟧ _ ⇒ _ of l high} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-lam x y z) (V-raw _) (V-raw _) = ⊑-lam x y z
stamp-val-prec {A = ` _ of l low} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ ⊑-const (V-raw x) (V-raw x₁) = ⊑-cast ⊑-const (⊑-base (prec-refl _))
stamp-val-prec {A = Ref (_ of l _) of l low} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-addr {gc = gc} {gc′} {ℓv} {ℓv′} a b) (V-raw V-addr) (V-raw V-addr)
  with cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-addr {gc = gc} {gc′} {ℓv} {ℓv′} {ℓ = low} a b)
... | ⟨ _ , _ , ⊑-ty l⊑l (⊑-ref A⊑A′) ⟩ =
  ⊑-cast (⊑-addr a b) (⊑-ref (prec-coerce-id A⊑A′) (prec-coerce-id A⊑A′) (prec-refl _))
stamp-val-prec {A = ⟦ _ ⟧ _ ⇒ _ of l low} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-lam {gc = gc} {gc′} {ℓv} {ℓv′} x y z) (V-raw _) (V-raw _)
  with cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-lam {gc = gc} {gc′} {ℓv} {ℓv′} {ℓ = low} x y z)
... | ⟨ _ , _ , ⊑-ty _ (⊑-fun g⊑g′ A⊑A′ B⊑B′) ⟩ =
  ⊑-cast (⊑-lam x y z) (⊑-fun (⊑-id g⊑g′) (prec-coerce-id A⊑A′) (prec-coerce-id B⊑B′) (prec-refl _))
stamp-val-prec {A = A} {A′} {ℓ = low} Γ⊑Γ′ Σ⊑Σ′ V⊑V′ (V-raw _) (V-raw _)
  rewrite stamp-low A | stamp-low A′ = V⊑V′
stamp-val-prec {A = T of ⋆} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-castr V⊑V′ A⊑c′) (V-raw v) (V-cast v′ i′) =
  case ⟨ v , cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ V⊑V′ ⟩ of λ where
  ⟨ V-const , () , _ ⟩
  ⟨ V-addr , () , _ ⟩
  ⟨ V-ƛ , () , _ ⟩
stamp-val-prec {A = T of l high} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-castr V⊑V′ A⊑c′) (V-raw v) (V-cast v′ i′) =
  ⊑-castr V⊑V′ (stamp-ir-high-on-high-right A⊑c′ i′)
stamp-val-prec {A = T of l low} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-castr V⊑V′ A⊑c′) (V-raw v) (V-cast v′ i′) =
  ⊑-cast V⊑V′  (stamp-ir-high-on-low-right A⊑c′ i′)
stamp-val-prec {A = A} {A′} {ℓ = low} Γ⊑Γ′ Σ⊑Σ′ (⊑-castr V⊑V′ A⊑c′) (V-raw x) (V-cast x₁ i)
  rewrite stamp-low A with i
... | ir-base {g = g} _ _ rewrite g⋎̃low≡g {g} = ⊑-castr V⊑V′ A⊑c′
... | ir-ref {g = g} _ rewrite g⋎̃low≡g {g} = ⊑-castr V⊑V′ A⊑c′
... | ir-fun {g = g} _ rewrite g⋎̃low≡g {g} = ⊑-castr V⊑V′ A⊑c′
stamp-val-prec {A′ = T of ⋆} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-castl V⊑V′ c⊑A′) (V-cast v i) (V-raw v′) =
  case ⟨ v′ , cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ V⊑V′ ⟩ of λ where
  ⟨ V-const , _ , () ⟩
  ⟨ V-addr , _ , () ⟩
  ⟨ V-ƛ , _ , () ⟩
stamp-val-prec {A′ = T of l high} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-castl V⊑V′ c⊑A′) (V-cast v i) (V-raw v′) =
  ⊑-castl V⊑V′ (stamp-ir-high-on-high-left c⊑A′ i)
stamp-val-prec {A′ = T of l low} {ℓ = high} Γ⊑Γ′ Σ⊑Σ′ (⊑-castl V⊑V′ c⊑A′) (V-cast v i) (V-raw v′) =
  ⊑-cast V⊑V′ (stamp-ir-high-on-low-left c⊑A′ i)
stamp-val-prec {A = A} {A′} {ℓ = low} Γ⊑Γ′ Σ⊑Σ′ (⊑-castl V⊑V′ c⊑A′) (V-cast v i) (V-raw v′)
  rewrite stamp-low A′ with i
... | ir-base {g = g} _ _ rewrite g⋎̃low≡g {g} = ⊑-castl V⊑V′ c⊑A′
... | ir-ref {g = g} _ rewrite g⋎̃low≡g {g} = ⊑-castl V⊑V′ c⊑A′
... | ir-fun {g = g} _ rewrite g⋎̃low≡g {g} = ⊑-castl V⊑V′ c⊑A′
stamp-val-prec {A = A} {A′} {ℓ = ℓ} Γ⊑Γ′ Σ⊑Σ′ (⊑-cast V⊑V′ c⊑c′) (V-cast v i) (V-cast v′ i′) =
  ⊑-cast V⊑V′ (stamp-ir-prec c⊑c′ i i′)
stamp-val-prec {A = A} {A′} {ℓ = ℓ} Γ⊑Γ′ Σ⊑Σ′ (⊑-castl (⊑-castr V⊑V′ A⊑c′) c⊑A′) (V-cast v i) (V-cast v′ i′) =
  ⊑-cast V⊑V′ (stamp-ir-prec (comp-pres-prec-rl A⊑c′ c⊑A′) i i′)
stamp-val-prec {A = A} {A′} {ℓ = ℓ} Γ⊑Γ′ Σ⊑Σ′ (⊑-castr (⊑-castl V⊑V′ c⊑A′) A⊑c′) (V-cast v i) (V-cast v′ i′) =
  ⊑-cast V⊑V′ (stamp-ir-prec (comp-pres-prec-lr c⊑A′ A⊑c′) i i′)
stamp-val-prec _ _ V⊑W v V-● = contradiction V⊑W (_ ⋤●)
stamp-val-prec _ _ V⊑W V-● w = contradiction V⊑W (●⋤ _)
