module LabelCoercionCalculi.CoercionExp where

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

data ⊢_⇒_ : Label → Label → Set where

  id : ∀ g → ⊢ g ⇒ g

  ↑ : ⊢ l low ⇒ l high

  _! : ∀ ℓ → ⊢ l ℓ ⇒ ⋆

  _??_ : ∀ ℓ (p : BlameLabel) → ⊢ ⋆ ⇒ l ℓ


infixl 8 _⨾_  {- syntactic composition -}

data CoercionExp_⇒_ : Label → Label → Set where

  id : ∀ g → CoercionExp g ⇒ g

  _⨾_ : ∀ {g₁ g₂ g₃} → CoercionExp g₁ ⇒ g₂ → ⊢ g₂ ⇒ g₃ → CoercionExp g₁ ⇒ g₃

  ⊥ : ∀ g₁ g₂ (p : BlameLabel) → CoercionExp g₁ ⇒ g₂


-- data 𝒱 : ∀ {g₁ g₂} → CoercionExp g₁ ⇒ g₂ → Set where

--   id : ∀ {g} → 𝒱 (id g)

--   up : 𝒱 ((id (l low)) ⨾ ↑)

--   inj : ∀ {ℓ} → 𝒱 ((id (l ℓ)) ⨾ (ℓ !))

--   proj : ∀ {ℓ p} → 𝒱 ((id ⋆) ⨾ (ℓ ?? p))

--   up-inj : 𝒱 ((id (l low)) ⨾ ↑ ⨾ (high !))

--   proj-up : ∀ {p} → 𝒱 ((id ⋆) ⨾ (low ?? p) ⨾ ↑)

--   proj-inj : ∀ {ℓ p} → 𝒱 ((id ⋆) ⨾ (ℓ ?? p) ⨾ (ℓ !))

--   proj-up-inj : ∀ {p} → 𝒱 ((id ⋆) ⨾ (low ?? p) ⨾ ↑ ⨾ (high !))

data 𝒱 : ∀ {g₁ g₂} → CoercionExp g₁ ⇒ g₂ → Set where

  id : ∀ {g} → 𝒱 (id g)

  id⨾? : ∀ {ℓ p} → 𝒱 ((id ⋆) ⨾ (ℓ ?? p))

  inj : ∀ {g ℓ} {c̅ : CoercionExp g ⇒ l ℓ} → 𝒱 c̅ → 𝒱 (c̅ ⨾ (ℓ !))

  up : ∀ {g} {c̅ : CoercionExp g ⇒ l low} → 𝒱 c̅ → 𝒱 (c̅ ⨾ ↑)


infix 2 _—→_

data _—→_ : ∀ {g₁ g₂} → CoercionExp g₁ ⇒ g₂ → CoercionExp g₁ ⇒ g₂ → Set where

  ξ : ∀ {g₁ g₂ g₃} {c̅ c̅′ : CoercionExp g₁ ⇒ g₂} {c : ⊢ g₂ ⇒ g₃}
    → c̅  —→ c̅′
      ----------------------
    → c̅ ⨾ c  —→ c̅′ ⨾ c

  ξ-⊥ : ∀ {p} {g₁ g₂ g₃} {c : ⊢ g₂ ⇒ g₃}
      ------------------------------------------
    → (⊥ g₁ g₂ p) ⨾ c  —→ ⊥ g₁ g₃ p

  id : ∀ {g₁ g₂} {c̅ : CoercionExp g₁ ⇒ g₂}
    → 𝒱 c̅
      --------------------------
    → c̅ ⨾ (id g₂)  —→ c̅

  ?-id : ∀ {p} {g ℓ} {c̅ : CoercionExp g ⇒ (l ℓ)}
    → 𝒱 c̅
      ----------------------------------
    → c̅ ⨾ (ℓ !) ⨾ (ℓ ?? p)  —→ c̅

  ?-↑ : ∀ {p} {g} {c̅ : CoercionExp g ⇒ (l low)}
    → 𝒱 c̅
      ---------------------------------------
    → c̅ ⨾ (low !) ⨾ (high ?? p)  —→ c̅ ⨾ ↑

  ?-⊥ : ∀ {p} {g} {c̅ : CoercionExp g ⇒ (l high)}
    → 𝒱 c̅
      -----------------------------------------------
    → c̅ ⨾ (high !) ⨾ (low ?? p)  —→ ⊥ g (l low) p

infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {g₁ g₂} (c̅₁ c̅₂ : CoercionExp g₁ ⇒ g₂) → Set where
  _∎ : ∀ {g₁ g₂} (c̅ : CoercionExp g₁ ⇒ g₂)
      ---------------
    → c̅ —↠ c̅

  _—→⟨_⟩_ : ∀ {g₁ g₂} (c̅₁ : CoercionExp g₁ ⇒ g₂) {c̅₂ c̅₃}
    → c̅₁ —→ c̅₂
    → c̅₂ —↠ c̅₃
      ---------------
    → c̅₁ —↠ c̅₃

plug-cong : ∀ {g₁ g₂ g₃} {M N : CoercionExp g₁ ⇒ g₂} {c : ⊢ g₂ ⇒ g₃}
  → M —↠ N
  → M ⨾ c —↠ N ⨾ c
plug-cong (M ∎) = (M ⨾ _) ∎
plug-cong (M —→⟨ M→L ⟩ L↠N) = M ⨾ _ —→⟨ ξ M→L ⟩ (plug-cong L↠N)

↠-trans : ∀ {g₁ g₂} {L M N : CoercionExp g₁ ⇒ g₂}
  → L —↠ M
  → M —↠ N
  → L —↠ N
↠-trans (L ∎) (._ ∎) = L ∎
↠-trans (L ∎) (.L —→⟨ M→ ⟩ ↠N) = L —→⟨ M→ ⟩ ↠N
↠-trans (L —→⟨ L→ ⟩ ↠M) (M ∎) = L —→⟨ L→ ⟩ ↠M
↠-trans (L —→⟨ L→ ⟩ ↠M) (M —→⟨ M→ ⟩ ↠N) = L —→⟨ L→ ⟩ ↠-trans ↠M (M —→⟨ M→ ⟩ ↠N)


data Progress : ∀ {g₁ g₂} → (c̅ : CoercionExp g₁ ⇒ g₂) → Set where

  done : ∀ {g₁ g₂} {c̅ : CoercionExp g₁ ⇒ g₂}
    → 𝒱 c̅
    → Progress c̅

  error : ∀ {p} {g₁ g₂} → Progress (⊥ g₁ g₂ p)

  step : ∀ {g₁ g₂} {c̅ c̅′ : CoercionExp g₁ ⇒ g₂}
    → c̅  —→ c̅′
    → Progress c̅


-- progress : ∀ {g₁ g₂} (c̅ : CoercionExp g₁ ⇒ g₂) → Progress c̅
-- progress (id g) = done id
-- progress (c̅ ⨾ c) with progress c̅
-- ... | step c̅→c̅′ = step (ξ c̅→c̅′)
-- ... | error = step ξ-⊥
-- ... | done id with c
-- progress (_ ⨾ c) | done id | id g = step (id id)
-- progress (_ ⨾ c) | done id | ↑ = done up
-- progress (_ ⨾ c) | done id | ℓ ! = done inj
-- progress (_ ⨾ c) | done id | ℓ ?? p = done proj
-- progress (_ ⨾ c) | done up with c
-- progress (_ ⨾ c) | done up | id (l high) = step (id up)
-- progress (_ ⨾ c) | done up | high ! = done up-inj
-- progress (_ ⨾ c) | done inj with c
-- progress (_ ⨾ c) | done inj | id ⋆ = step (id inj)
-- progress (_ ⨾ c) | done (inj {low})  | low ?? p  = step (?-id id)
-- progress (_ ⨾ c) | done (inj {high}) | high ?? p = step (?-id id)
-- progress (_ ⨾ c) | done (inj {low})  | high ?? p = step (?-↑ id)
-- progress (_ ⨾ c) | done (inj {high}) | low ?? p  = step (?-⊥ id)
-- progress (_ ⨾ c) | done proj with c
-- progress (_ ⨾ c) | done proj | id (l ℓ) = step (id proj)
-- progress (_ ⨾ c) | done proj | ℓ ! = done proj-inj
-- progress (_ ⨾ c) | done proj | ↑ = done proj-up
-- progress (_ ⨾ c) | done up-inj with c
-- progress (_ ⨾ c) | done up-inj | id ⋆ = step (id up-inj)
-- progress (_ ⨾ c) | done up-inj | low ?? p = step (?-⊥ up)
-- progress (_ ⨾ c) | done up-inj | high ?? p = step (?-id up)
-- progress (_ ⨾ c) | done proj-up with c
-- progress (_ ⨾ c) | done proj-up | id _ = step (id proj-up)
-- progress (_ ⨾ c) | done proj-up | high ! = done proj-up-inj
-- progress (_ ⨾ c) | done proj-inj with c
-- progress (_ ⨾ c) | done proj-inj | id ⋆ = step (id proj-inj)
-- progress (_ ⨾ c) | done (proj-inj {low}) | low ?? p = step (?-id proj)
-- progress (_ ⨾ c) | done (proj-inj {high}) | low ?? p = step (?-⊥ proj)
-- progress (_ ⨾ c) | done (proj-inj {low}) | high ?? p = step (?-↑ proj)
-- progress (_ ⨾ c) | done (proj-inj {high}) | high ?? p = step (?-id proj)
-- progress (_ ⨾ c) | done proj-up-inj with c
-- progress (_ ⨾ c) | done proj-up-inj | id ⋆ = step (id proj-up-inj)
-- progress (_ ⨾ c) | done proj-up-inj | low ?? p = step (?-⊥ proj-up)
-- progress (_ ⨾ c) | done proj-up-inj | high ?? p = step (?-id proj-up)
-- progress (⊥ g₁ g₂ p) = error

progress : ∀ {g₁ g₂} (c̅ : CoercionExp g₁ ⇒ g₂) → Progress c̅
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

infix 4 ⊢_⊑_

data ⊢_⊑_ : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CoercionExp g₁ ⇒ g₂) (c̅′ : CoercionExp g₁′ ⇒ g₂′) → Set where

  ⊑-id : ∀ {g g′}
    → (g⊑g′ : g ⊑ₗ g′)
      ---------------------------------
    → ⊢ id g ⊑ id g′

  ⊑-cast : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
             {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
             {c : ⊢ g₂ ⇒ g₃} {c′ : ⊢ g₂′ ⇒ g₃′}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₃′ {- c ⊑ c′ -}
      -------------------------------------------
    → ⊢ c̅ ⨾ c ⊑ c̅′ ⨾ c′

  ⊑-castl : ∀ {g₁ g₁′ g₂ g₂′ g₃}
              {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
              {c : ⊢ g₂ ⇒ g₃}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₂′  {- c ⊑ g₂′ -}
      -------------------------------------------
    → ⊢ c̅ ⨾ c ⊑ c̅′

  ⊑-castr : ∀ {g₁ g₁′ g₂ g₂′ g₃′}
              {c̅ : CoercionExp g₁ ⇒ g₂} {c̅′ : CoercionExp g₁′ ⇒ g₂′}
              {c′ : ⊢ g₂′ ⇒ g₃′}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₂ ⊑ₗ g₃′  {- g₂ ⊑ c′ -}
      -------------------------------------------
    → ⊢ c̅ ⊑ c̅′ ⨾ c′

  ⊑-⊥ : ∀ {g₁ g₁′ g₂ g₂′} {c̅ : CoercionExp g₁ ⇒ g₂} {p}
    → g₁ ⊑ₗ g₁′
    → g₂ ⊑ₗ g₂′
      ---------------------------------
    → ⊢ c̅ ⊑ ⊥ g₁′ g₂′ p

prec→⊑ : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CoercionExp g₁ ⇒ g₂) (c̅′ : CoercionExp g₁′ ⇒ g₂′)
  → ⊢ c̅ ⊑ c̅′
  → ((g₁ ⊑ₗ g₁′) × (g₂ ⊑ₗ g₂′))
prec→⊑ (id g) (id g′) (⊑-id g⊑g′) = ⟨ g⊑g′ , g⊑g′ ⟩
prec→⊑ (c̅ ⨾ c) (c̅′ ⨾ c′) (⊑-cast c̅⊑c̅′ _ g₂⊑g₂′) =
  case prec→⊑ c̅ c̅′ c̅⊑c̅′ of λ where
  ⟨ g₁⊑g₁′ , _ ⟩ → ⟨ g₁⊑g₁′ , g₂⊑g₂′ ⟩
prec→⊑ (c̅ ⨾ c) c̅′ (⊑-castl c̅⊑c̅′ g₂⊑g₂′ g₃⊑g₂′) =
  case prec→⊑ c̅ c̅′ c̅⊑c̅′ of λ where
  ⟨ g₁⊑g₁′ , _ ⟩ → ⟨ g₁⊑g₁′ , g₃⊑g₂′ ⟩
prec→⊑ c̅ (c̅′ ⨾ c′) (⊑-castr c̅⊑c̅′ g₂⊑g₂′ g₂⊑g₃′) =
  case prec→⊑ c̅ c̅′ c̅⊑c̅′ of λ where
  ⟨ g₁⊑g₁′ , _ ⟩ → ⟨ g₁⊑g₁′ , g₂⊑g₃′ ⟩
prec→⊑ c̅ (⊥ _ _ _) (⊑-⊥ g₁⊑g₁′ g₂⊑g₂′) = ⟨ g₁⊑g₁′ , g₂⊑g₂′ ⟩


catchup : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CoercionExp g₁ ⇒ g₂) (c̅′ : CoercionExp g₁′ ⇒ g₂′)
  → 𝒱 c̅′
  → ⊢ c̅ ⊑ c̅′
    -------------------------------------------------
  → ∃[ c̅ₙ ] (𝒱 c̅ₙ ) × (c̅ —↠ c̅ₙ) × (⊢ c̅ₙ ⊑ c̅′)

catchup-to-id : ∀ {g₁ g₂ g′}
  → (c̅₁ : CoercionExp g₁ ⇒ g₂)
  → ⊢ c̅₁ ⊑ id g′
  → ∃[ c̅₂ ] (𝒱 c̅₂) × (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ id g′)
catchup-to-id (id _) (⊑-id g⊑g′) = ⟨ id _ , id , id _ ∎ , ⊑-id g⊑g′ ⟩
catchup-to-id (c̅ ⨾ ↑) (⊑-castl c̅⊑id low⊑g′ high⊑g′) =
  case ⟨ low⊑g′ , high⊑g′ ⟩ of λ where
  ⟨ l⊑l , () ⟩  {- g′ can't be high and low at the same time -}
catchup-to-id (c̅ ⨾ ℓ ?? p) (⊑-castl c̅⊑id ⋆⊑ (l⊑l {ℓ}))
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , id {⋆} , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ id ⋆ ⨾ ℓ ?? p , id⨾? , plug-cong c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ ℓ₀ ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id ⟩
catchup-to-id (c̅ ⨾ ℓ !) (⊑-castl c̅⊑id (l⊑l {ℓ}) ⋆⊑)
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ c̅ₙ ⨾ ℓ ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩
catchup-to-id (c̅ ⨾ id g) (⊑-castl c̅⊑id _ _)
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩  =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑id ⟩


catchup-to-inj : ∀ {g₁ g₂ g′ ℓ′}
  → (c̅   : CoercionExp g₁ ⇒ g₂  )
  → (c̅ₙ′ : CoercionExp g′ ⇒ l ℓ′)
  → 𝒱 c̅ₙ′
  → ⊢ c̅ ⊑ c̅ₙ′ ⨾ ℓ′ !
    -----------------------------------------------------
  → ∃[ c̅ₙ ] (𝒱 c̅ₙ) × (c̅ —↠ c̅ₙ) × (⊢ c̅ₙ ⊑ c̅ₙ′ ⨾ ℓ′ !)
catchup-to-inj (c̅ ⨾ ℓ !) c̅ₙ′ v′ (⊑-cast c̅⊑c̅ₙ′ (l⊑l {ℓ}) ⋆⊑)
  with catchup c̅ c̅ₙ′ v′ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ ⨾ ℓ ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑c̅ₙ′ l⊑l ⋆⊑ ⟩
catchup-to-inj (c̅ ⨾ id ⋆) c̅ₙ′ v′ (⊑-cast  c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-inj c̅ c̅ₙ′ v′ (⊑-castr c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′ ⟩
catchup-to-inj (c̅ ⨾ id ⋆) c̅ₙ′ v′ (⊑-castl c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-inj c̅ c̅ₙ′ v′ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′ ⟩
catchup-to-inj c̅ c̅ₙ′ v′ (⊑-castr c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup c̅ c̅ₙ′ v′ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ , v , c̅↠c̅ₙ , ⊑-castr c̅ₙ⊑c̅ₙ′ ⋆⊑ ⋆⊑ ⟩


catchup-to-id⨾? : ∀ {g₁ g₂ ℓ′} {p}
  → (c̅   : CoercionExp g₁ ⇒ g₂)
  → ⊢ c̅ ⊑ id ⋆ ⨾ ℓ′ ?? p
    --------------------------------------------------------
  → ∃[ c̅ₙ ] (𝒱 c̅ₙ) × (c̅ —↠ c̅ₙ) × (⊢ c̅ₙ ⊑ id ⋆ ⨾ ℓ′ ?? p)
catchup-to-id⨾? (c̅ ⨾ id ⋆) (⊑-cast c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-id c̅ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , ⊑-castr c̅ₙ⊑id ⋆⊑ ⋆⊑ ⟩
catchup-to-id⨾? (c̅ ⨾ ℓ ?? p) (⊑-cast c̅⊑c̅ₙ′ ⋆⊑ l⊑l)
  with catchup-to-id c̅ c̅⊑c̅ₙ′
... | ⟨ id ⋆ , id , c̅↠c̅ₙ , ⊑-id ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ ℓ ?? p , id⨾? , plug-cong c̅↠c̅ₙ , ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ ℓ₀ ! , inj v , c̅↠c̅ₙ , ⊑-castl _ () ⋆⊑ ⟩  {- impossible -}
catchup-to-id⨾? (c̅ ⨾ c) (⊑-castl c̅⊑c̅ₙ′ g₃⊑ℓ′ g₂⊑ℓ′)
  with catchup-to-id⨾? c̅ c̅⊑c̅ₙ′ | g₃⊑ℓ′ | g₂⊑ℓ′ | c
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | ⋆⊑ | ⋆⊑ | c = {!!}
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | l⊑l {ℓ′} | ⋆⊑ | c = {!!}
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | l⊑l {ℓ′} | l⊑l {ℓ′} | c = {!!}
... | ⟨ id ⋆ , id , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | ⋆⊑ | l⊑l {ℓ′} | c = {!!}
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castl _ () ⋆⊑) ⋆⊑ ⋆⊑ ⟩ | ⋆⊑ | l⊑l {low} | low ?? p    {- impossible -}
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id⨾? _ _ ⟩ | ⋆⊑ | l⊑l {low} | low ?? p =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾? ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castl _ () ⋆⊑) ⋆⊑ ⋆⊑ ⟩ | ⋆⊑ | l⊑l {high} | high ?? p {- impossible -}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id⨾? _ _ ⟩ | ⋆⊑ | l⊑l {high} | high ?? p =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾? ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | ⋆⊑ | l⊑l {high} | c = {!!}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | ⋆⊑ | l⊑l {low} | c = {!!}

catchup-to-id⨾? c̅ (⊑-castr c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-id c̅ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ = ⟨ c̅ₙ , v , c̅↠c̅ₙ , ⊑-castr c̅ₙ⊑id ⋆⊑ ⋆⊑ ⟩


catchup c̅ (id g′) id c̅⊑id = catchup-to-id c̅ c̅⊑id
catchup c̅ (c̅ₙ′ ⨾ ℓ′ !) (inj v′) c̅⊑c̅′ = catchup-to-inj c̅ c̅ₙ′ v′ c̅⊑c̅′
catchup c̅ (id ⋆ ⨾ ℓ′ ?? p) id⨾? c̅⊑c̅′ = {!!}
catchup c̅ (c̅ₙ′ ⨾ ↑)   (up  v′) c̅⊑c̅′ = {!!}
