module LabelExpr.Security where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
  renaming (_∎ to _∎ₗ ; _—→⟨_⟩_ to _—→ₗ⟨_⟩_)
  hiding (Progress; progress; plug-cong; ↠-trans)
open import CoercionExpr.SyntacComp
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SecurityLevel renaming (∥_∥ to ∥_∥ₗ)
open import CoercionExpr.Stamping
open import LabelExpr.LabelExpr


stampₑ-security : ∀ {V ℓ} (v : LVal V) → (∥ V ∥ v) ⋎ ℓ ≡ ∥ stampₑ V v ℓ ∥ (stampₑ-LVal v)
stampₑ-security {V = l ℓ}    {ℓ = low}  v-l rewrite ℓ⋎low≡ℓ {ℓ} = refl
stampₑ-security {V = l low}  {ℓ = high} v-l = refl
stampₑ-security {V = l high} {ℓ = high} v-l = refl
stampₑ-security {V} {low}  (v-cast (ir 𝓋 _)) = stampₗ-security _ 𝓋 low
stampₑ-security {V} {high} (v-cast (ir 𝓋 _)) = stampₗ-security _ 𝓋 high

security-eqₑ : ∀ {V₁ V₂}
  → (v₁ : LVal V₁)
  → (v₂ : LVal V₂)
  → V₁ ≡ V₂
    --------------------------
  → ∥ V₁ ∥ v₁ ≡ ∥ V₂ ∥ v₂
security-eqₑ v₁ v₂ eq rewrite eq rewrite uniq-LVal v₁ v₂ = refl


cast-security : ∀ {ℓ g V V′} {c̅ : CExpr l ℓ ⇒ g}
  → (v : LVal V)
  → ⊢ V ⇐ l ℓ
  → V ⟪ c̅ ⟫ —↠ₑ V′
  → (v′ : LVal V′)
    -------------------------
  → ∥ V ∥ v ≼ ∥ V′ ∥ v′
cast-security v-l ⊢V (l _ ⟪ id (l _) ⟫ —→⟨ β-id ⟩ _ ∎) v-l = ≼-refl
cast-security v-l ⊢V (l _ ⟪ _ ⟫ —→⟨ cast c̅→⁺c̅ₙ 𝓋 ⟩ ↠V′) v-l =
  cast-security v-l ⊢l ↠V′ v-l
cast-security v-l ⊢V (l _ ⟪ _ ⟫ —→⟨ blame _ ⟩ _ —→⟨ r ⟩ _) v-l =
  contradiction r (LResult⌿→ fail)
cast-security v-l ⊢V ↠V′ (v-cast (ir id x)) = contradiction refl (recompute (¬? (_ ==? _)) x)
cast-security v-l ⊢l ↠V′ (v-cast (ir (inj id) _))
  with preserve-mult (⊢cast ⊢l) ↠V′
... | ⊢cast ⊢l with cast-red-label-eq ↠V′
...   | refl = ≡→≼ refl
cast-security v-l ⊢V ↠V′ (v-cast (ir (inj (up id)) x₁)) = _ ≼high
cast-security v-l ⊢l ↠V′ (v-cast (ir (up id) x)) = _ ≼high
cast-security (v-cast i) ⊢V (_ —→⟨ ξ ℓ⟨c̅⟩→N ⟩ _) v-l =
  contradiction ℓ⟨c̅⟩→N (LVal⌿→ (v-cast i))
cast-security (v-cast (ir id x)) (⊢cast ⊢l) (_ —→⟨ comp i† ⟩ r*) v-l =
  contradiction refl (recompute (¬? (_ ==? _)) x)
cast-security (v-cast (ir (up id) _)) (⊢cast ⊢l)
              (_ —→⟨ comp i† ⟩ _ —→⟨ cast r _ ⟩ _ —→⟨ β-id ⟩ _ ∎) v-l =
  comp-security (up id) (→⁺-impl-↠ r) id
cast-security (v-cast (ir (up id) _)) (⊢cast ⊢l)
              (_ —→⟨ comp i† ⟩ _ —→⟨ cast _ 𝓋 ⟩ _ —→⟨ cast (_ —→ₗ⟨ r ⟩ _) _ ⟩ _) v-l =
  contradiction r (CVal⌿→ 𝓋)
cast-security (v-cast (ir (up id) _)) (⊢cast ⊢l)
              (_ —→⟨ comp i† ⟩ _ —→⟨ cast x y ⟩ _ —→⟨ blame _ ⟩ _ —→⟨ r ⟩ _) v-l =
  contradiction r (LResult⌿→ fail)
cast-security (v-cast (ir (up id) _)) (⊢cast ⊢l)
              (_ —→⟨ comp i† ⟩ _ —→⟨ blame _ ⟩ _ —→⟨ r ⟩ _) v-l =
  contradiction r (LResult⌿→ fail)
cast-security (v-cast i) ⊢V (l _ ⟪ _ ⟫ ⟪ _ ⟫ —→⟨ ξ ℓ⟨c⟩→N ⟩ ↠V′) (v-cast x₁) =
  contradiction ℓ⟨c⟩→N (LVal⌿→ (v-cast i))
cast-security (v-cast (ir 𝓋 _)) ⊢V
              (l _ ⟪ _ ⟫ ⟪ _ ⟫ —→⟨ comp i ⟩ ↠V′) (v-cast (ir 𝓋′ _))
  with preserve-mult (⊢cast ⊢l) ↠V′
... | ⊢cast ⊢l with cast-red-label-eq ↠V′
...   | refl = comp-security 𝓋 (cast-red-inv ↠V′) 𝓋′


stamp⇒⋆-security : ∀ {g ℓ V V′}
  → (v : LVal V)
  → ⊢ V ⇐ g
  → stampₑ V v ℓ ⟪ coerce (g ⋎̃ l ℓ) ⇒⋆ ⟫ —↠ₑ V′
  → (v′ : LVal V′)
    ---------------------------------
  → (∥ V ∥ v) ⋎ ℓ ≡ ∥ V′ ∥ v′
stamp⇒⋆-security {ℓ = low} (v-l {ℓ}) ⊢l ↠V′ v′
  rewrite ℓ⋎low≡ℓ {ℓ} with ↠V′
... | _ —→⟨ r ⟩ _ = contradiction r (LVal⌿→ (v-cast (ir (inj id) (λ ()))))
... | _ ∎ with v′
... | v-cast (ir (inj id) _) = refl
stamp⇒⋆-security {ℓ = high} {V} {V′} (v-l {low}) ⊢l ↠V′ v′ = ∣V†∣≡∣V′∣
  where
  ♣ : (id (l low) ⨾ ↑ ⨾ id (l high) ⨾ high !) —→⁺ (id (l low) ⨾ ↑ ⨾ high !)
  ♣ = _ —→ₗ⟨ ξ (id (up id)) ⟩ _ ∎ₗ
  ♥ : l low ⟪ id (l low) ⨾ ↑ ⟫ ⟪ id (l high) ⨾ (high !) ⟫ —↠ₑ l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  ♥ = _ —→⟨ comp (ir (up id) (λ ())) ⟩ _ —→⟨ cast ♣ (inj (up id)) ⟩ _ ∎
  V† = l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj (up id)) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = high} (v-l {high}) ⊢l (_ ∎) (v-cast (ir (inj id) _)) = refl
stamp⇒⋆-security {ℓ = high} (v-l {high}) ⊢l (_ —→⟨ V→M ⟩ _) v′ =
  contradiction V→M (LVal⌿→ (v-cast (ir (inj id) (λ ()))))
stamp⇒⋆-security {ℓ = low} (v-cast {ℓ} {l ℓ} {id (l ℓ)} (ir id x)) ⊢V ↠V′ v′ =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stamp⇒⋆-security {ℓ = low} {V} {V′} (v-cast {ℓ} {⋆} {_ ⨾ _ !} (ir (inj id) _)) (⊢cast ⊢l) ↠V′ v′
  rewrite ℓ⋎low≡ℓ {ℓ} = ∣V†∣≡∣V′∣
  where
  ♥ : l ℓ ⟪ id (l ℓ) ⨾ ℓ ! ⟫ ⟪ id ⋆ ⟫ —↠ₑ l ℓ ⟪ id (l ℓ) ⨾ ℓ ! ⟫
  ♥ = _ —→⟨ comp (ir (inj id) (λ ())) ⟩ _ —→⟨ cast (_ —→ₗ⟨ id (inj id) ⟩ _ ∎ₗ) (inj id) ⟩ _ ∎
  V† = l ℓ ⟪ id (l ℓ) ⨾ ℓ ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj id) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = low} {V} {V′} (v-cast {low} {⋆} {id (l low) ⨾ ↑ ⨾ high !} (ir (inj (up id)) _)) (⊢cast ⊢l) ↠V′ v′ =
  ∣V†∣≡∣V′∣
  where
  ♥ : l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫ ⟪ id ⋆ ⟫ —↠ₑ l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  ♥ = _ —→⟨ comp (ir (inj (up id)) (λ ())) ⟩ _ —→⟨ cast (_ —→ₗ⟨ id (inj (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩ _ ∎
  V† = l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj (up id)) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = low} {V} {V′} (v-cast {low} {l high} {id (l low) ⨾ ↑} (ir (up id) _)) (⊢cast ⊢l) ↠V′ v′ =
  ∣V†∣≡∣V′∣
  where
  ♥ : l low ⟪ id (l low) ⨾ ↑ ⟫ ⟪ id (l high) ⨾ high ! ⟫ —↠ₑ l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  ♥ = _ —→⟨ comp (ir (up id) (λ ())) ⟩
      _ —→⟨ cast (_ —→ₗ⟨ ξ (id (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
      _ ∎
  V† = l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj (up id)) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = high} (v-cast {c̅ = id (l low)} (ir id x)) (⊢cast ⊢l) ↠V′ v′ =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stamp⇒⋆-security {ℓ = high} {V} {V′} (v-cast {c̅ = id (l high)} (ir id _)) (⊢cast ⊢l) ↠V′ v′ =
  ∣V†∣≡∣V′∣
  where
  ♥ : l high ⟪ id (l high) ⟫ ⟪ id (l high) ⨾ high ! ⟫ —↠ₑ l high ⟪ id (l high) ⨾ high ! ⟫
  ♥ = _ —→⟨ ξ β-id ⟩ _ ∎
  V† = l high ⟪ id (l high) ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj id) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = high} {V} {V′} (v-cast {c̅ = id _ ⨾ low !} (ir (inj id) _)) (⊢cast ⊢l) ↠V′ v′ =
  ∣V†∣≡∣V′∣
  where
  ♥ : l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫ ⟪ id ⋆ ⟫ —↠ₑ l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  ♥ = _ —→⟨ comp (ir (inj (up id)) (λ ())) ⟩
      _ —→⟨ cast (_ —→ₗ⟨ id (inj (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
      _ ∎
  V† = l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj (up id)) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = high} {V} {V′} (v-cast {c̅ = id _ ⨾ high !} (ir (inj id) _)) (⊢cast ⊢l) ↠V′ v′ =
  ∣V†∣≡∣V′∣
  where
  ♥ : l high ⟪ id (l high) ⨾ high ! ⟫ ⟪ id ⋆ ⟫ —↠ₑ l high ⟪ id (l high) ⨾ high ! ⟫
  ♥ = _ —→⟨ comp (ir (inj id) (λ ())) ⟩
      _ —→⟨ cast (_ —→ₗ⟨ id (inj id) ⟩ _ ∎ₗ) (inj id) ⟩
      _ ∎
  V† = l high ⟪ id (l high) ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj id) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = high} {V} {V′} (v-cast {c̅ = _ ⨾ _ !} (ir (inj (up id)) _)) (⊢cast ⊢l) ↠V′ v′ =
  ∣V†∣≡∣V′∣
  where
  ♥ : l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫ ⟪ id ⋆ ⟫ —↠ₑ l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  ♥ = _ —→⟨ comp (ir (inj (up id)) (λ ())) ⟩
      _ —→⟨ cast (_ —→ₗ⟨ id (inj (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
      _ ∎
  V† = l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj (up id)) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
stamp⇒⋆-security {ℓ = high} {V} {V′} (v-cast {c̅ = _ ⨾ ↑} (ir (up id) _)) (⊢cast ⊢l) ↠V′ v′ =
  ∣V†∣≡∣V′∣
  where
  ♥ : l low ⟪ id (l low) ⨾ ↑ ⟫ ⟪ id (l high) ⨾ high ! ⟫ —↠ₑ l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  ♥ = _ —→⟨ comp (ir (up id) (λ ())) ⟩
      _ —→⟨ cast (_ —→ₗ⟨ ξ (id (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
      _ ∎
  V† = l low ⟪ id (l low) ⨾ ↑ ⨾ high ! ⟫
  v† : LVal V†
  v† = v-cast (ir (inj (up id)) (λ ()))
  eq : V† ≡ V′
  eq = det-multₑ ♥ ↠V′ (success v†) (success v′)
  ∣V†∣≡∣V′∣ : ∥ V† ∥ v† ≡ ∥ V′ ∥ v′
  ∣V†∣≡∣V′∣ = security-eqₑ v† v′ eq
