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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; subst)
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


cast-security : ∀ {g g′ V V′} {c̅ : CExpr g ⇒ g′}
  → (v : LVal V)
  → ⊢ V ⇐ g
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
cast-security (v-cast (ir v _)) (⊢cast ⊢l) (_ —→⟨ comp i† ⟩ r) v-l
  with cast-to-label-inv r | preserve-mult (⊢cast ⊢l) r
... | ⟨ refl , r* ⟩ | ⊢l =
  let comp-red = cast-red-inv r* in
  comp-security v comp-red id
cast-security (v-cast i) ⊢V
              (l _ ⟪ _ ⟫ ⟪ _ ⟫ —→⟨ ξ ℓ⟨c⟩→N ⟩ ↠V′) (v-cast _) =
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


stamp-cast-security : ∀ {g g′ ℓ V V′} {c̅ : CExpr (g ⋎̃ l ℓ) ⇒ g′}
  → (v : LVal V)
  → ⊢ V ⇐ g
  → stampₑ V v ℓ ⟪ c̅ ⟫ —↠ₑ V′
  → (v′ : LVal V′)
    ---------------------------------
  → (∥ V ∥ v) ⋎ ℓ ≼ ∥ V′ ∥ v′
stamp-cast-security {ℓ = ℓ} v ⊢V ↠V′ v′ =
  let eq  = stampₑ-security {ℓ = ℓ} v in
  let leq = cast-security (stampₑ-LVal v) (stampₑ-wt v ⊢V) ↠V′ v′ in
  ≼-trans (≡→≼ eq) leq

stamp⇒⋆-cast-security : ∀ {g g′ ℓ V V′} {c̅ : CExpr ⋆ ⇒ g′}
  → (v : LVal V)
  → ⊢ V ⇐ g
  → stampₑ V v ℓ ⟪ coerce (g ⋎̃ l ℓ) ⇒⋆ ⟫ ⟪ c̅ ⟫ —↠ₑ V′
  → (v′ : LVal V′)
    ---------------------------------
  → (∥ V ∥ v) ⋎ ℓ ≼ ∥ V′ ∥ v′
stamp⇒⋆-cast-security {g} {g′} {ℓ} {V} {V′} {c̅} v ⊢V ↠V′ v′ =
  case lexpr-sn (stampₑ V v ℓ ⟪ coerce (g ⋎̃ l ℓ) ⇒⋆ ⟫) (⊢cast (stampₑ-wt v ⊢V)) of λ where
  ⟨ W , ↠W , success w ⟩ →
    let eq = stamp⇒⋆-security v ⊢V ↠W w in
    let ⊢W = preserve-mult (⊢cast (stampₑ-wt v ⊢V)) ↠W in
    case lexpr-sn (W ⟪ c̅ ⟫) (⊢cast ⊢W) of λ where
    ⟨ W′ , ↠W′ , success w′ ⟩ →
      let leq = cast-security w ⊢W ↠W′ w′ in
      let r*  = ↠ₑ-trans (plug-congₑ ↠W) ↠W′ in
      ≼-trans (≡→≼ eq) (subst (_ ≼_)
        (security-eqₑ w′ v′ (det-multₑ r* ↠V′ (success w′) (success v′))) leq)
    ⟨ blame q , ↠blameq , fail ⟩ →
      let r* = ↠ₑ-trans (plug-congₑ ↠W) ↠blameq in
      let eq = det-multₑ ↠V′ r* (success v′) fail in
      case (subst LVal eq v′) of λ ()
  ⟨ blame p , ↠blamep , fail ⟩ →
    let r* = ↠ₑ-trans (plug-congₑ ↠blamep) (_ —→⟨ ξ-blame ⟩ _ ∎) in
    let eq = det-multₑ ↠V′ r* (success v′) fail in
    case (subst LVal eq v′) of λ ()

security-prec-mono : ∀ {g g′} {V W}
  → (v : LVal V)
  → (w : LVal W)
  → ⊢ V ⊑ W ⇐ g ⊑ g′
    -----------------------------------
  → ∥ V ∥ v ≼ ∥ W ∥ w
security-prec-mono v-l v-l ⊑-l = ≼-refl
security-prec-mono v-l (v-cast (ir 𝓋′ _)) (⊑-castr ⊑-l ℓ⊑c̅′) =
  ≡→≼ (security-prec-right _ 𝓋′ ℓ⊑c̅′)
security-prec-mono (v-cast (ir 𝓋 _)) v-l (⊑-castl ⊑-l c̅⊑ℓ′) =
  ≡→≼ (security-prec-left _ 𝓋 c̅⊑ℓ′)
security-prec-mono (v-cast (ir 𝓋 _)) (v-cast (ir 𝓋′ _)) V⊑W
  with prec→⊢ V⊑W
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv V⊑W
... | ⟨ refl , c̅⊑c̅′ ⟩ =
  security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′
