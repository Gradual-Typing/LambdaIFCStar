module CoercionExpr.CoercionExpr where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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


coerceₗ : ∀ {g₁ g₂} → g₁ ≾ g₂ → (p : BlameLabel) → CExpr g₁ ⇒ g₂
coerceₗ {⋆} {⋆}   _ p = id ⋆
coerceₗ {⋆} {l ℓ} ≾-⋆l p = id ⋆ ⨾ ℓ ?? p
coerceₗ {l ℓ} {⋆} ≾-⋆r p = id (l ℓ) ⨾ ℓ !
coerceₗ {l low}  {l low}  (≾-l l≼l) p = id (l low)
coerceₗ {l low}  {l high} (≾-l l≼h) p = id (l low) ⨾ ↑
coerceₗ {l high} {l high} (≾-l h≼h) p = id (l high)


-- data 𝒱 : ∀ {g₁ g₂} → CExpr g₁ ⇒ g₂ → Set where

--   id : ∀ {g} → 𝒱 (id g)

--   up : 𝒱 ((id (l low)) ⨾ ↑)

--   inj : ∀ {ℓ} → 𝒱 ((id (l ℓ)) ⨾ (ℓ !))

--   proj : ∀ {ℓ p} → 𝒱 ((id ⋆) ⨾ (ℓ ?? p))

--   up-inj : 𝒱 ((id (l low)) ⨾ ↑ ⨾ (high !))

--   proj-up : ∀ {p} → 𝒱 ((id ⋆) ⨾ (low ?? p) ⨾ ↑)

--   proj-inj : ∀ {ℓ p} → 𝒱 ((id ⋆) ⨾ (ℓ ?? p) ⨾ (ℓ !))

--   proj-up-inj : ∀ {p} → 𝒱 ((id ⋆) ⨾ (low ?? p) ⨾ ↑ ⨾ (high !))

data 𝒱 : ∀ {g₁ g₂} → CExpr g₁ ⇒ g₂ → Set where

  id : ∀ {g} → 𝒱 (id g)

  id⨾? : ∀ {ℓ p} → 𝒱 ((id ⋆) ⨾ (ℓ ?? p))

  inj : ∀ {g ℓ} {c̅ : CExpr g ⇒ l ℓ} → 𝒱 c̅ → 𝒱 (c̅ ⨾ (ℓ !))

  up : ∀ {g} {c̅ : CExpr g ⇒ l low} → 𝒱 c̅ → 𝒱 (c̅ ⨾ ↑)


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
    → 𝒱 c̅
      --------------------------
    → c̅ ⨾ (id g₂)  —→ c̅

  ?-id : ∀ {p} {g ℓ} {c̅ : CExpr g ⇒ (l ℓ)}
    → 𝒱 c̅
      ----------------------------------
    → c̅ ⨾ (ℓ !) ⨾ (ℓ ?? p)  —→ c̅

  ?-↑ : ∀ {p} {g} {c̅ : CExpr g ⇒ (l low)}
    → 𝒱 c̅
      ---------------------------------------
    → c̅ ⨾ (low !) ⨾ (high ?? p)  —→ c̅ ⨾ ↑

  ?-⊥ : ∀ {p} {g} {c̅ : CExpr g ⇒ (l high)}
    → 𝒱 c̅
      -----------------------------------------------
    → c̅ ⨾ (high !) ⨾ (low ?? p)  —→ ⊥ g (l low) p

infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {g₁ g₂} (c̅₁ c̅₂ : CExpr g₁ ⇒ g₂) → Set where
  _∎ : ∀ {g₁ g₂} (c̅ : CExpr g₁ ⇒ g₂)
      ---------------
    → c̅ —↠ c̅

  _—→⟨_⟩_ : ∀ {g₁ g₂} (c̅₁ : CExpr g₁ ⇒ g₂) {c̅₂ c̅₃}
    → c̅₁ —→ c̅₂
    → c̅₂ —↠ c̅₃
      ---------------
    → c̅₁ —↠ c̅₃

plug-cong : ∀ {g₁ g₂ g₃} {M N : CExpr g₁ ⇒ g₂} {c : ⊢ g₂ ⇒ g₃}
  → M —↠ N
  → M ⨾ c —↠ N ⨾ c
plug-cong (M ∎) = (M ⨾ _) ∎
plug-cong (M —→⟨ M→L ⟩ L↠N) = M ⨾ _ —→⟨ ξ M→L ⟩ (plug-cong L↠N)

↠-trans : ∀ {g₁ g₂} {L M N : CExpr g₁ ⇒ g₂}
  → L —↠ M
  → M —↠ N
  → L —↠ N
↠-trans (L ∎) (._ ∎) = L ∎
↠-trans (L ∎) (.L —→⟨ M→ ⟩ ↠N) = L —→⟨ M→ ⟩ ↠N
↠-trans (L —→⟨ L→ ⟩ ↠M) (M ∎) = L —→⟨ L→ ⟩ ↠M
↠-trans (L —→⟨ L→ ⟩ ↠M) (M —→⟨ M→ ⟩ ↠N) = L —→⟨ L→ ⟩ ↠-trans ↠M (M —→⟨ M→ ⟩ ↠N)


data Progress : ∀ {g₁ g₂} → (c̅ : CExpr g₁ ⇒ g₂) → Set where

  done : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂}
    → 𝒱 c̅
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



data Result : ∀ {g₁ g₂} → (c̅ : CExpr g₁ ⇒ g₂) → Set where

  success : ∀ {g₁ g₂} {c̅ c̅′ : CExpr g₁ ⇒ g₂}
    → c̅ —↠ c̅′
    → 𝒱 c̅′
    → Result c̅

  fail : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂} {p}
    → c̅ —↠ ⊥ g₁ g₂ p
    → Result c̅


result : ∀ {g₁ g₂} (c̅ : CExpr g₁ ⇒ g₂) → Result c̅
result (id g) = success (_ ∎) id
result (⊥ g₁ g₂ p) = fail (_ ∎)
result (c̅ ⨾ c) with result c̅
... | success c̅′↠c̅″ id with c
result (_ ⨾ c) | success c̅′↠c̅″ id | id g   =
  success (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id id ⟩ _ ∎)) id
result (_ ⨾ c) | success c̅′↠c̅″ id | ↑     =
  success (plug-cong c̅′↠c̅″) (up id)
result (_ ⨾ c) | success c̅′↠c̅″ id | ℓ !    =
  success (plug-cong c̅′↠c̅″) (inj id)
result (_ ⨾ c) | success c̅′↠c̅″ id | ℓ ?? p =
  success (plug-cong c̅′↠c̅″) id⨾?
result (_ ⨾ c) | success c̅′↠c̅″ id⨾? with c
result (_ ⨾ c) | success c̅′↠c̅″ id⨾? | id _ =
  success (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id id⨾? ⟩ _ ∎)) id⨾?
result (_ ⨾ c) | success c̅′↠c̅″ id⨾? | ↑   =
  success (plug-cong c̅′↠c̅″) (up id⨾?)
result (_ ⨾ c) | success c̅′↠c̅″ id⨾? | ℓ₁ ! =
  success (plug-cong c̅′↠c̅″) (inj id⨾?)
result (_ ⨾ c) | success c̅′↠c̅″ (inj v) with c
result (_ ⨾ c) | success c̅′↠c̅″ (inj v) | id ⋆ =
  success (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id (inj v) ⟩ _ ∎)) (inj v)
result (_ ⨾ c) | success c̅′↠c̅″ (inj {ℓ = low}  v) | low  ?? p =
  success (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-id v ⟩ _ ∎)) v
result (_ ⨾ c) | success c̅′↠c̅″ (inj {ℓ = high} v) | high ?? p =
  success (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-id v ⟩ _ ∎)) v
result (_ ⨾ c) | success c̅′↠c̅″ (inj {ℓ = low}  v) | high ?? p =
  success (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-↑ v ⟩ _ ∎)) (up v)
result (_ ⨾ c) | success c̅′↠c̅″ (inj {ℓ = high} v) | low  ?? p =
  fail (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ ?-⊥ v ⟩ _ ∎))
result (_ ⨾ c) | success c̅′↠c̅″ (up v) with c
result (_ ⨾ c) | success c̅′↠c̅″ (up v) | id (l high) =
  success (↠-trans (plug-cong c̅′↠c̅″) (_ —→⟨ id (up v) ⟩ _ ∎)) (up v)
result (_ ⨾ c) | success c̅′↠c̅″ (up v) | high !      =
  success (plug-cong c̅′↠c̅″) (inj (up v))
result (_ ⨾ c) | fail c̅′↠⊥ =
  fail (↠-trans (plug-cong c̅′↠⊥) (_ —→⟨ ξ-⊥ ⟩ _ ∎))
