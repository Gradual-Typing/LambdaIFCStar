module CoercionExpr.CoercionExpr where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.Coercions public


infixl 8 _⨾_  {- syntactic composition -}

data CExpr_⇒_ : Label → Label → Set where

  id : ∀ g → CExpr g ⇒ g

  _⨾_ : ∀ {g₁ g₂ g₃} → CExpr g₁ ⇒ g₂ → ⊢ g₂ ⇒ g₃ → CExpr g₁ ⇒ g₃

  ⊥ : ∀ g₁ g₂ (p : BlameLabel) → CExpr g₁ ⇒ g₂


coerce_⇒⋆ : ∀ g → CExpr g ⇒ ⋆
coerce_⇒⋆    ⋆  = id ⋆
coerce_⇒⋆ (l ℓ) = id (l ℓ) ⨾ ℓ !

coerce-≼ : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≼ ℓ₂ → CExpr l ℓ₁ ⇒ l ℓ₂
coerce-≼ l≼l = id (l low)
coerce-≼ l≼h = id (l low) ⨾ ↑
coerce-≼ h≼h = id (l high)

coerceₗ : ∀ {g₁ g₂} → g₁ ≾ g₂ → BlameLabel → CExpr g₁ ⇒ g₂
coerceₗ {g}    {⋆}    _           _ = coerce g ⇒⋆
coerceₗ {l ℓ₁} {l ℓ₂} (≾-l ℓ₁≼ℓ₂) _ = coerce-≼ ℓ₁≼ℓ₂
coerceₗ {⋆}    {l ℓ}  ≾-⋆l        p = id ⋆ ⨾ ℓ ?? p

coerce-<:ₗ : ∀ {g₁ g₂} → g₁ <:ₗ g₂ → CExpr g₁ ⇒ g₂
coerce-<:ₗ <:-⋆ = id ⋆
coerce-<:ₗ (<:-l ℓ₁≼ℓ₂) = coerce-≼ ℓ₁≼ℓ₂


-- data CVal : ∀ {g₁ g₂} → CExpr g₁ ⇒ g₂ → Set where

--   id : ∀ {g} → CVal (id g)

--   up : CVal ((id (l low)) ⨾ ↑)

--   inj : ∀ {ℓ} → CVal ((id (l ℓ)) ⨾ (ℓ !))

--   proj : ∀ {ℓ p} → CVal ((id ⋆) ⨾ (ℓ ?? p))

--   up-inj : CVal ((id (l low)) ⨾ ↑ ⨾ (high !))

--   proj-up : ∀ {p} → CVal ((id ⋆) ⨾ (low ?? p) ⨾ ↑)

--   proj-inj : ∀ {ℓ p} → CVal ((id ⋆) ⨾ (ℓ ?? p) ⨾ (ℓ !))

--   proj-up-inj : ∀ {p} → CVal ((id ⋆) ⨾ (low ?? p) ⨾ ↑ ⨾ (high !))

data CVal : ∀ {g₁ g₂} → CExpr g₁ ⇒ g₂ → Set where

  id : ∀ {g} → CVal (id g)

  id⨾? : ∀ {ℓ p} → CVal ((id ⋆) ⨾ (ℓ ?? p))

  inj : ∀ {g ℓ} {c̅ : CExpr g ⇒ l ℓ} → CVal c̅ → CVal (c̅ ⨾ (ℓ !))

  up : ∀ {g} {c̅ : CExpr g ⇒ l low} → CVal c̅ → CVal (c̅ ⨾ ↑)


infix 2 _—→_

data _—→_ : ∀ {g₁ g₂} → CExpr g₁ ⇒ g₂ → CExpr g₁ ⇒ g₂ → Set where

  ξ : ∀ {g₁ g₂ g₃} {c̅ c̅′ : CExpr g₁ ⇒ g₂} {c : ⊢ g₂ ⇒ g₃}
    → c̅  —→ c̅′
      ----------------------
    → c̅ ⨾ c  —→ c̅′ ⨾ c

  ξ-⊥ : ∀ {p} {g₁ g₂ g₃} {c : ⊢ g₂ ⇒ g₃}
      ------------------------------------------
    → (⊥ g₁ g₂ p) ⨾ c  —→ ⊥ g₁ g₃ p

  id : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂}
    → CVal c̅
      --------------------------
    → c̅ ⨾ (id g₂)  —→ c̅

  ?-id : ∀ {p} {g ℓ} {c̅ : CExpr g ⇒ (l ℓ)}
    → CVal c̅
      ----------------------------------
    → c̅ ⨾ (ℓ !) ⨾ (ℓ ?? p)  —→ c̅

  ?-↑ : ∀ {p} {g} {c̅ : CExpr g ⇒ (l low)}
    → CVal c̅
      ---------------------------------------
    → c̅ ⨾ (low !) ⨾ (high ?? p)  —→ c̅ ⨾ ↑

  ?-⊥ : ∀ {p} {g} {c̅ : CExpr g ⇒ (l high)}
    → CVal c̅
      -----------------------------------------------
    → c̅ ⨾ (high !) ⨾ (low ?? p)  —→ ⊥ g (l low) p


open import Common.MultiStep Label (CExpr_⇒_) _—→_ public

data _—→⁺_ : ∀ {g₁ g₂} (M N : CExpr g₁ ⇒ g₂) → Set where

  _—→⟨_⟩_ : ∀ {g₁ g₂} (L : CExpr g₁ ⇒ g₂) {M N}
    → L —→ M
    → M —↠ N
    → L —→⁺ N

→⁺-impl-↠ : ∀ {g₁ g₂} {M N : CExpr g₁ ⇒ g₂}
  → M —→⁺ N
  → M —↠  N
→⁺-impl-↠ (_ —→⟨ r ⟩ r*) = _ —→⟨ r ⟩ r*

plug-cong : ∀ {g₁ g₂ g₃} {M N : CExpr g₁ ⇒ g₂} {c : ⊢ g₂ ⇒ g₃}
  → M —↠ N
  → M ⨾ c —↠ N ⨾ c
plug-cong (M ∎) = (M ⨾ _) ∎
plug-cong (M —→⟨ M→L ⟩ L↠N) = M ⨾ _ —→⟨ ξ M→L ⟩ (plug-cong L↠N)


data Progress : ∀ {g₁ g₂} → (c̅ : CExpr g₁ ⇒ g₂) → Set where

  done : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂}
    → CVal c̅
    → Progress c̅

  error : ∀ {p} {g₁ g₂} → Progress (⊥ g₁ g₂ p)

  step : ∀ {g₁ g₂} {c̅ c̅′ : CExpr g₁ ⇒ g₂}
    → c̅  —→ c̅′
    → Progress c̅


progress : ∀ {g₁ g₂} (c̅ : CExpr g₁ ⇒ g₂) → Progress c̅
progress (id g) = done id
progress (c̅ ⨾ c) with progress c̅
... | step c̅→c̅′ = step (ξ c̅→c̅′)
... | error = step ξ-⊥
... | done id with c
progress (_ ⨾ c) | done id | id g   = step (id id)
progress (_ ⨾ c) | done id | ↑     = done (up id)
progress (_ ⨾ c) | done id | ℓ !    = done (inj id)
progress (_ ⨾ c) | done id | ℓ ?? p = done id⨾?
progress (_ ⨾ c) | done id⨾? with c
progress (_ ⨾ c) | done id⨾? | id _ = step (id id⨾?)
progress (_ ⨾ c) | done id⨾? | ↑   = done (up id⨾?)
progress (_ ⨾ c) | done id⨾? | ℓ₁ ! = done (inj id⨾?)
progress (_ ⨾ c) | done (inj v) with c
progress (_ ⨾ c) | done (inj v) | id ⋆ = step (id (inj v))
progress (_ ⨾ c) | done (inj {ℓ = low}  v) | low  ?? p = step (?-id v)
progress (_ ⨾ c) | done (inj {ℓ = high} v) | high ?? p = step (?-id v)
progress (_ ⨾ c) | done (inj {ℓ = low}  v) | high ?? p = step (?-↑ v)
progress (_ ⨾ c) | done (inj {ℓ = high} v) | low  ?? p = step (?-⊥ v)
progress (_ ⨾ c) | done (up v) with c
progress (_ ⨾ c) | done (up v) | id (l high) = step (id (up v))
progress (_ ⨾ c) | done (up v) | high !      = done (inj (up v))
progress (⊥ g₁ g₂ p) = error



data CResult : ∀ {g₁ g₂} → (c̅ : CExpr g₁ ⇒ g₂) → Set where

  success : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂} → CVal c̅ → CResult c̅

  fail    : ∀ {g₁ g₂ p} → CResult (⊥ g₁ g₂ p)


cexpr-sn : ∀ {g₁ g₂} (c̅ : CExpr g₁ ⇒ g₂) → ∃[ d̅ ] (c̅ —↠ d̅) × CResult d̅
cexpr-sn (id g) = ⟨ _ , _ ∎ , success id ⟩
cexpr-sn (⊥ g₁ g₂ p) = ⟨ _ , _ ∎ , fail ⟩
cexpr-sn (c̅ ⨾ c)
  with cexpr-sn c̅
... | ⟨ _ , c̅′↠c̅″ , success id ⟩
  with c
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id ⟩ | id g   =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id id ⟩ _ ∎) , success id ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id ⟩ | ↑     =
  ⟨ _ , plug-cong c̅′↠c̅″ , success (up id) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id ⟩ | ℓ !    =
  ⟨ _ , plug-cong c̅′↠c̅″ , success (inj id) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id ⟩ | ℓ ?? p =
  ⟨ _ , plug-cong c̅′↠c̅″ , success id⨾? ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id⨾? ⟩
  with c
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id⨾? ⟩ | id _ =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id id⨾? ⟩ _ ∎) , success id⨾? ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id⨾? ⟩ | ↑   =
  ⟨ _ , plug-cong c̅′↠c̅″ , success (up id⨾?) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success id⨾? ⟩ | ℓ₁ ! =
  ⟨ _ , plug-cong c̅′↠c̅″ , success (inj id⨾?) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (inj v) ⟩
  with c
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (inj v) ⟩ | id ⋆ =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id (inj v) ⟩ _ ∎) , success (inj v) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (inj {ℓ = low}  v) ⟩ | low  ?? p =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-id v ⟩ _ ∎) , success v ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (inj {ℓ = high} v) ⟩ | high ?? p =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-id v ⟩ _ ∎) , success v ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (inj {ℓ = low}  v) ⟩ | high ?? p =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-↑ v ⟩ _ ∎) , success (up v) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (inj {ℓ = high} v) ⟩ | low  ?? p =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-⊥ v ⟩ _ ∎) , fail ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (up v) ⟩
  with c
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (up v) ⟩ | id (l high) =
  ⟨ _ , ↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id (up v) ⟩ _ ∎) , success (up v) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠c̅″ , success (up v) ⟩ | high !      =
  ⟨ _ , plug-cong c̅′↠c̅″ , success (inj (up v)) ⟩
cexpr-sn (_ ⨾ c) | ⟨ _ , c̅′↠⊥ , fail ⟩ =
  ⟨ _ , ↠-trans (plug-cong c̅′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎) , fail ⟩

uniq-CVal : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂} → (v v′ : CVal c̅) → v ≡ v′
uniq-CVal id id = refl
uniq-CVal id⨾? id⨾? = refl
uniq-CVal (inj v) (inj v′) rewrite uniq-CVal v v′ = refl
uniq-CVal (up v) (up v′) rewrite uniq-CVal v v′ = refl

CVal⌿→ : ∀ {g₁ g₂} {c̅ d̅ : CExpr g₁ ⇒ g₂} → CVal c̅ → ¬ (c̅ —→ d̅)
CVal⌿→ id ()
CVal⌿→ (inj 𝓋) (ξ r) = CVal⌿→ 𝓋 r
CVal⌿→ (up 𝓋)  (ξ r) = CVal⌿→ 𝓋 r
CVal⌿→ id⨾? (ξ ())

CResult⌿→ : ∀ {ℓ g} {c̅ d̅ : CExpr l ℓ ⇒ g} → CResult c̅ → ¬ (c̅ —→ d̅)
CResult⌿→ (success 𝓋) = CVal⌿→ 𝓋

det : ∀ {ℓ g} {c̅ d̅₁ d̅₂ : CExpr l ℓ ⇒ g}
  → c̅ —→ d̅₁
  → c̅ —→ d̅₂
    ---------------------------------------
  → d̅₁ ≡ d̅₂
det (ξ r1) (ξ r2) = cong (_⨾ _) (det r1 r2)
det (ξ r) (id 𝓋) = contradiction r (CVal⌿→ 𝓋)
det (ξ r) (?-id 𝓋) = contradiction r (CVal⌿→ (inj 𝓋))
det (ξ r) (?-↑ 𝓋) = contradiction r (CVal⌿→ (inj 𝓋))
det (ξ r) (?-⊥ 𝓋) = contradiction r (CVal⌿→ (inj 𝓋))
det ξ-⊥ ξ-⊥ = refl
det (id 𝓋) (ξ r) = contradiction r (CVal⌿→ 𝓋)
det (id _) (id _) = refl
det (?-id 𝓋) (ξ r) = contradiction r (CVal⌿→ (inj 𝓋))
det (?-id _) (?-id _) = refl
det (?-↑ 𝓋) (ξ r) = contradiction r (CVal⌿→ (inj 𝓋))
det (?-↑ _) (?-↑ _) = refl
det (?-⊥ 𝓋) (ξ r) = contradiction r (CVal⌿→ (inj 𝓋))
det (?-⊥ _) (?-⊥ _) = refl

det-mult : ∀ {ℓ g} {c̅ d̅₁ d̅₂ : CExpr l ℓ ⇒ g}
  → c̅ —↠ d̅₁
  → c̅ —↠ d̅₂
  → CResult d̅₁
  → CResult d̅₂
    ----------------------------------------------
  → d̅₁ ≡ d̅₂
det-mult (_ ∎) (_ ∎) r₁ r₂ = refl
det-mult (_ ∎) (_ —→⟨ c̅→d̅ ⟩ _) r₁ r₂ = contradiction c̅→d̅ (CResult⌿→ r₁)
det-mult (_ —→⟨ c̅→d̅ ⟩ _) (_ ∎) r₁ r₂ = contradiction c̅→d̅ (CResult⌿→ r₂)
det-mult (_ —→⟨ c̅→d̅₃ ⟩ d̅₃↠d̅₁) (_ —→⟨ c̅→d̅₄ ⟩ d̅₄↠d̅₂) r₁ r₂
  with det c̅→d̅₃ c̅→d̅₄
... | refl = det-mult d̅₃↠d̅₁ d̅₄↠d̅₂ r₁ r₂
