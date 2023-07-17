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

open import Syntax
open import Common.Utils
open import Memory.HeapContext
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CoercionExpr.Precision
open import CoercionExpr.CatchUp renaming (catchup to catchupₗ)

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
catchup {μ = μ} {PC} (V-raw v′) (⊑-castl {c = c} M⊑V′ c⊑A′) Γ⊑Γ′ Σ⊑Σ′
--   with cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑V′
-- ... | ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩
  with catchup {μ = μ} {PC} (V-raw v′) M⊑V′ Γ⊑Γ′ Σ⊑Σ′ | v′ | c
... | ⟨ V , V-raw V-const , M↠V , ⊑-const ⟩ | V-const | cast (id ι) c̅ =
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
    case c⊑A′ of λ where
    (⊑-base c̅⊑low) →
      case pres-prec-left-mult c̅⊑low c̅↠d̅ of λ where
      (⊑-cast _ () _)
  ⟨ _ , c̅↠↑ , success (up id) ⟩ →
    case c⊑A′ of λ where
    (⊑-base c̅⊑low) →
      case pres-prec-left-mult c̅⊑low c̅↠↑ of λ where
      (⊑-cast _ _ ())
  ⟨ ⊥ _ _ p , c̅↠⊥ , result ⟩ → {!!}
... | ⟨ V , V-raw V-addr , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
... | ⟨ V , V-raw V-ƛ , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
... | ⟨ V , V-cast v i , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
... | ⟨ V , V-● , M↠V , V⊑V′ ⟩ | v′ | c = {!!}
catchup (V-cast x x₁) M⊑V′ Γ⊑Γ′ Σ⊑Σ′ = {!!}
catchup V-● M⊑V′ Γ⊑Γ′ Σ⊑Σ′ = {!!}
