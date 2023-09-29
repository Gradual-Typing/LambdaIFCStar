module CoercionExpr.SecurityLevel where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
open import CoercionExpr.Precision
open import CoercionExpr.SyntacComp


∥_∥ : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → CVal c̅ → StaticLabel
∥ id (l ℓ) ∥ id = ℓ
∥ id (l ℓ) ⨾ ℓ ! ∥ (inj id) = ℓ
∥ id (l low) ⨾ ↑ ⨾ high ! ∥ (inj (up v)) = high
∥ id (l low) ⨾ ↑ ∥ (up v) = high

security-prec : ∀ {ℓ ℓ′ g g′} (c̅ : CExpr l ℓ ⇒ g) (c̅′ : CExpr l ℓ′ ⇒ g′)
  → (v : CVal c̅)
  → (v′ : CVal c̅′)
  → ⊢ c̅ ⊑ c̅′
    --------------------------------
  → ∥ c̅ ∥ v ≼ ∥ c̅′ ∥ v′
security-prec (id (l _)) (id (l _)) id id (⊑-id l⊑l) = ≼-refl
security-prec (id (l _)) (_ ⨾ (_ !)) id (inj v′) (⊑-castr _ _ ())
security-prec (id (l ℓ)) (id (l low) ⨾ ↑) id (up id) c̅⊑c̅′ = ℓ ≼high
security-prec (_ ⨾ (_ !)) (id (l _)) (inj id) id (⊑-castl c̅⊑c̅′ l⊑l ⋆⊑) = ≼-refl
security-prec (id (l low) ⨾ ↑ ⨾ (_ !)) (id (l high)) (inj (up id)) id (⊑-castl c̅⊑c̅′ l⊑l ⋆⊑) = h≼h
security-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj id) (inj id) (⊑-cast (⊑-id l⊑l) l⊑l _) = ≼-refl
security-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj id) (inj id) (⊑-castr (⊑-castl c̅⊑c̅′ l⊑l _) _ _) = ≼-refl
security-prec (_ ⨾ (ℓ !)) (_ ⨾ (_ !)) (inj id) (inj (up id)) c̅⊑c̅′ = ℓ ≼high
security-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj id) (⊑-cast (⊑-castl _ () _) l⊑l _)
security-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj (up id)) (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l _) = h≼h
security-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj (up id)) (⊑-cast (⊑-castr (⊑-castl _ _ ()) _ _) l⊑l _)
security-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj id) (⊑-castr (⊑-castl c̅⊑c̅′ l⊑l _) _ _) = h≼h
security-prec (_ ⨾ (_ !)) (_ ⨾ (_ !)) (inj (up id)) (inj (up id)) (⊑-castr c̅⊑c̅′ _ _) = h≼h
security-prec (_ ⨾ (ℓ !)) (_ ⨾ ↑) (inj id) (up id) c̅⊑c̅′ = ℓ ≼high
security-prec (_ ⨾ (_ !)) (_ ⨾ ↑) (inj (up id)) (up id) c̅⊑c̅′ = h≼h
security-prec (_ ⨾ ↑) .(id (l _)) (up id) id (⊑-castl c̅⊑c̅′ l⊑l ())
security-prec (_ ⨾ ↑) .(id (l _) ⨾ (_ !)) (up id) (inj id) (⊑-cast c̅⊑c̅′ l⊑l ())
security-prec (_ ⨾ ↑) .(id (l _) ⨾ (_ !)) (up id) (inj id) (⊑-castl c̅⊑c̅′ () _)
security-prec (_ ⨾ ↑) .(id (l _) ⨾ (_ !)) (up id) (inj id) (⊑-castr c̅⊑c̅′ _ ())
security-prec (_ ⨾ ↑) .(id (l low) ⨾ ↑ ⨾ (high !)) (up id) (inj (up id)) c̅⊑c̅′ = h≼h
security-prec (_ ⨾ ↑) .(id (l low) ⨾ ↑) (up id) (up id) c̅⊑c̅′ = h≼h


security-prec-left : ∀ {ℓ ℓ′ g} (c̅ : CExpr l ℓ ⇒ g)
  → (v : CVal c̅)
  → ⊢l c̅ ⊑ l ℓ′
    --------------------------------
  → ∥ c̅ ∥ v ≡ ℓ′
security-prec-left .(id (l _)) id (⊑-id l⊑l) = refl
security-prec-left .(id (l _) ⨾ (_ !)) (inj id) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) = refl
security-prec-left .(_ ⨾ ↑ ⨾ (high !)) (inj (up id)) (⊑-cast _ l⊑l _) = refl
security-prec-left .(_ ⨾ ↑) (up id) (⊑-cast _ l⊑l ())


security-prec-right : ∀ {ℓ ℓ′ g} (c̅ : CExpr l ℓ′ ⇒ g)
  → (v : CVal c̅)
  → ⊢r l ℓ ⊑ c̅
    --------------------------------
  → ℓ′ ≡ ∥ c̅ ∥ v
security-prec-right .(id (l _)) id (⊑-id l⊑l) = refl
security-prec-right .(id (l _) ⨾ (_ !)) (inj id) (⊑-cast (⊑-id l⊑l) l⊑l _) = refl
security-prec-right .(_ ⨾ ↑) (up id) (⊑-cast _ l⊑l ())


security-eq : ∀ {ℓ g} {c̅ d̅ : CExpr l ℓ ⇒ g}
  → (v₁ : CVal c̅)
  → (v₂ : CVal d̅)
  → c̅ ≡ d̅
    --------------------------
  → ∥ c̅ ∥ v₁ ≡ ∥ d̅ ∥ v₂
security-eq v₁ v₂ eq rewrite eq | uniq-CVal v₁ v₂ = refl

comp-security : ∀ {ℓ g₁ g₂} {c̅ₙ : CExpr l ℓ ⇒ g₁} {c̅ : CExpr g₁ ⇒ g₂} {d̅ₙ}
  → (v : CVal c̅ₙ)
  → c̅ₙ ⨟ c̅ —↠ d̅ₙ
  → (v′ : CVal d̅ₙ)
    -----------------------------
  → ∥ c̅ₙ ∥ v ≼ ∥ d̅ₙ ∥ v′
comp-security {c̅ₙ = c̅ₙ} {id g} {d̅ₙ} v r* v′ =
  ≡→≼ (security-eq v v′ (det-mult ♣ r* (success v) (success v′)))
  where
  ♣ : c̅ₙ ⨾ id g —↠ c̅ₙ
  ♣ = _ —→⟨ id v ⟩ _ ∎
comp-security {c̅ₙ = c̅ₙ} {c̅ ⨾ id g} v r* v′
  with cexpr-sn (c̅ₙ ⨟ c̅)
... | ⟨ ⊥ _ _ p , ↠⊥ , fail ⟩ =
  let ♣ = (↠-trans (plug-cong ↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎)) in
  let eq = det-mult r* ♣ (success v′) fail in
  case (subst CVal eq v′) of λ where ()
... | ⟨ d̅ , ↠d̅ , success v-d ⟩ =
  let ♣ : (c̅ₙ ⨟ c̅) ⨾ id g —↠ d̅
      ♣ = ↠-trans (plug-cong ↠d̅) (_ —→⟨ id v-d ⟩ _ ∎) in
  let eq = det-mult ♣ r* (success v-d) (success v′) in
  let ih = comp-security v ↠d̅ v-d in
  subst (_ ≼_) (security-eq v-d v′ eq) ih
comp-security {c̅ₙ = c̅ₙ} {c̅ ⨾ ↑} v r* v′
  with cexpr-sn (c̅ₙ ⨟ c̅)
... | ⟨ ⊥ _ _ p , ↠⊥ , fail ⟩ =
  let ♣ = (↠-trans (plug-cong ↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎)) in
  let eq = det-mult r* ♣ (success v′) fail in
  case (subst CVal eq v′) of λ where ()
... | ⟨ id (l low) , ↠d̅ , success id ⟩ =
  let ♣ : (c̅ₙ ⨟ c̅) ⨾ ↑ —↠ id (l low) ⨾ ↑
      ♣ = plug-cong ↠d̅ in
  let eq = det-mult ♣ r* (success (up id)) (success v′) in
  subst (_ ≼_) (security-eq (up id) v′ eq) (_ ≼high)
comp-security {c̅ₙ = c̅ₙ} {c̅ ⨾ ℓ !} v r* v′
  with cexpr-sn (c̅ₙ ⨟ c̅)
... | ⟨ ⊥ _ _ p , ↠⊥ , fail ⟩ =
  let ♣ = (↠-trans (plug-cong ↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎)) in
  let eq = det-mult r* ♣ (success v′) fail in
  case (subst CVal eq v′) of λ where ()
... | ⟨ id (l ℓ) , ↠d̅ , success id ⟩ =
  let ih = comp-security v ↠d̅ id in
  let ♣ : (c̅ₙ ⨟ c̅) ⨾ ℓ ! —↠ id (l ℓ) ⨾ ℓ !
      ♣ = plug-cong ↠d̅ in
  let eq = det-mult ♣ r* (success (inj id)) (success v′) in
  subst (_ ≼_) (security-eq (inj id) v′ eq) ih
... | ⟨ id (l low) ⨾ ↑ , ↠d̅ , success (up id) ⟩ =
  let ♣ : (c̅ₙ ⨟ c̅) ⨾ high ! —↠ id (l low) ⨾ ↑ ⨾ high !
      ♣ = plug-cong ↠d̅ in
  let eq = det-mult ♣ r* (success (inj (up id))) (success v′) in
  subst (_ ≼_) (security-eq (inj (up id)) v′ eq) (_ ≼high)
comp-security {c̅ₙ = c̅ₙ} {c̅ ⨾ low ?? p} v r* v′
  with cexpr-sn (c̅ₙ ⨟ c̅)
... | ⟨ ⊥ _ _ p , ↠⊥ , fail ⟩ =
  let ♣ = (↠-trans (plug-cong ↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎)) in
  let eq = det-mult r* ♣ (success v′) fail in
  case (subst CVal eq v′) of λ where ()
... | ⟨ d̅ , ↠d̅ , success (inj (id {l low})) ⟩ =
  let ih = comp-security v ↠d̅ (inj id) in
  ℓ≼low→ℓ≼ℓ′ ih
... | ⟨ d̅ , ↠d̅ , success (inj (id {l high})) ⟩ =
  case v′ of λ where ()
... | ⟨ d̅ , ↠d̅ , success (inj (up id)) ⟩ =
  let ♣ = (↠-trans (plug-cong ↠d̅) (_ —→⟨ ?-⊥ (up id) ⟩ _ ∎)) in
  let eq = det-mult r* ♣ (success v′) fail in
  case (subst CVal eq v′) of λ where ()
comp-security {c̅ₙ = c̅ₙ} {c̅ ⨾ high ?? p} {d̅ₙ} v r* v′
  with cexpr-sn (c̅ₙ ⨟ c̅)
... | ⟨ ⊥ _ _ p , ↠⊥ , fail ⟩ =
  let ♣ = (↠-trans (plug-cong ↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎)) in
  let eq = det-mult r* ♣ (success v′) fail in
  case (subst CVal eq v′) of λ where ()
... | ⟨ d̅ , ↠d̅ , success (inj (id {l low})) ⟩ =
  let ♣ = (↠-trans (plug-cong ↠d̅) (_ —→⟨ ?-↑ id ⟩ _ ∎)) in
  let eq = det-mult ♣ r* (success (up id)) (success v′) in
  subst (_ ≼_) (security-eq (up id) v′ eq) (_ ≼high)
... | ⟨ d̅ , ↠d̅ , success (inj (id {l high})) ⟩ =
  let ♣ = (↠-trans (plug-cong ↠d̅) (_ —→⟨ ?-id id ⟩ _ ∎)) in
  let eq = det-mult ♣ r* (success id) (success v′) in
  subst (_ ≼_) (security-eq id v′ eq) (_ ≼high)
... | ⟨ d̅ , ↠d̅ , success (inj (up id)) ⟩ =
  let ♣ = (↠-trans (plug-cong ↠d̅) (_ —→⟨ ?-id (up id) ⟩ _ ∎)) in
  let eq = det-mult ♣ r* (success (up id)) (success v′) in
  subst (_ ≼_) (security-eq (up id) v′ eq) (_ ≼high)
comp-security {c̅ = ⊥ _ _ p} v (_ ∎) ()

-- If a coercion expr has a static type, then its security level is equal to the type
static-security : ∀ {ℓ₁ ℓ₂} → (c̅ : CExpr l ℓ₁ ⇒ l ℓ₂) → (𝓋 : CVal c̅) → ∥ c̅ ∥ 𝓋 ≡ ℓ₂
static-security (id (l ℓ))        id      = refl
static-security (id (l low) ⨾ ↑) (up id) = refl
