module LabelExpr.LabelExpr where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
  hiding (Progress; progress; plug-cong; ↠-trans)
open import CoercionExpr.SyntacComp
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)


data LExpr : Set where

  l : StaticLabel → LExpr

  _⟪_⟫ : ∀ {g₁ g₂} → LExpr → CExpr g₁ ⇒ g₂ → LExpr

  blame : BlameLabel → LExpr


Irreducible : ∀ {g₁ g₂} (c̅ : CExpr g₁ ⇒ g₂) → Set
Irreducible {g₁} {g₂} c̅ = CVal c̅ × g₁ ≢ g₂


data LVal : LExpr → Set where

  {- raw value -}
  v-l : ∀ {ℓ} → LVal (l ℓ)

  {- wrapped value (one cast) -}
  v-cast : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g}
    → Irreducible c̅
    → LVal (l ℓ ⟪ c̅ ⟫)

data ⊢_⇐_ : LExpr → Label → Set where

  ⊢l : ∀ {ℓ} → ⊢ l ℓ ⇐ l ℓ

  ⊢cast : ∀ {g₁ g₂} {M} {c̅ : CExpr g₁ ⇒ g₂}
    → ⊢ M ⇐ g₁
      ------------------
    → ⊢ M ⟪ c̅ ⟫ ⇐ g₂

  ⊢blame : ∀ {g} {p} → ⊢ blame p ⇐ g


infix 2 _—→ₑ_

data _—→ₑ_ : (M N : LExpr) → Set where

  ξ : ∀ {g₁ g₂} {M N} {c̅ : CExpr g₁ ⇒ g₂}
    → M —→ₑ N
      --------------------------
    → M ⟪ c̅ ⟫ —→ₑ N ⟪ c̅ ⟫

  ξ-blame : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂} {p}
      -----------------------------------------------
    → blame p ⟪ c̅ ⟫ —→ₑ blame p

  β-id : ∀ {ℓ} → l ℓ ⟪ id (l ℓ) ⟫ —→ₑ l ℓ

  cast : ∀ {ℓ g} {c̅ c̅ₙ : CExpr l ℓ ⇒ g}
    → c̅ —↠ c̅ₙ
    → CVal c̅ₙ
      -------------------------------
    → l ℓ ⟪ c̅ ⟫ —→ₑ l ℓ ⟪ c̅ₙ ⟫

  blame : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g} {p}
    → c̅ —↠ ⊥ (l ℓ) g p
      --------------------------
    → l ℓ ⟪ c̅ ⟫ —→ₑ blame p

  comp : ∀ {ℓ g₁ g₂} {c̅ᵢ : CExpr l ℓ ⇒ g₁} {d̅ : CExpr g₁ ⇒ g₂}
    → Irreducible c̅ᵢ
      -------------------------------------------
    → l ℓ ⟪ c̅ᵢ ⟫ ⟪ d̅ ⟫ —→ₑ l ℓ ⟪ c̅ᵢ ⨟ d̅ ⟫



data Progress : LExpr → Set where

  done : ∀ {M} → LVal M → Progress M

  error : ∀ {p} → Progress (blame p)

  step : ∀ {M N} → M  —→ₑ N → Progress M

progress : ∀ {g M} → ⊢ M ⇐ g → Progress M
progress ⊢l = done v-l
progress (⊢cast {c̅ = c̅} ⊢M) =
  case progress ⊢M of λ where
  (done v) →
    case ⟨ v , ⊢M ⟩ of λ where
    ⟨ v-l , ⊢l ⟩ →
      case result c̅ of λ where
      (success c̅↠d̅ 𝓋) → step (cast c̅↠d̅ 𝓋)
      (fail c̅↠⊥)      → step (blame c̅↠⊥)
    ⟨ v-cast {c̅ = c̅′} i , ⊢cast _ ⟩ → step (comp i)
  (error) → step ξ-blame
  (step M→N) → step (ξ M→N)
progress ⊢blame = error

preserve : ∀ {g M N}
  → ⊢ M ⇐ g
  → M —→ₑ N
  → ⊢ N ⇐ g
preserve (⊢cast ⊢M) (ξ M→N) = ⊢cast (preserve ⊢M M→N)
preserve (⊢cast ⊢M) ξ-blame = ⊢blame
preserve (⊢cast ⊢M) β-id = ⊢l
preserve (⊢cast ⊢M) (cast x x₁) = ⊢cast ⊢l
preserve (⊢cast ⊢M) (blame _) = ⊢blame
preserve (⊢cast ⊢M) (comp _) = ⊢cast ⊢l


infix  2 _—↠ₑ_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠ₑ_ : ∀ (M N : LExpr) → Set where
  _∎ : ∀ M → M —↠ₑ M

  _—→⟨_⟩_ : ∀ L {M N : LExpr}
    → L —→ₑ M
    → M —↠ₑ N
      ---------------
    → L —↠ₑ N

plug-congₑ : ∀ {g₁ g₂} {M N } {c̅ : CExpr g₁ ⇒ g₂}
  → M —↠ₑ N
  → M ⟪ c̅ ⟫ —↠ₑ N ⟪ c̅ ⟫
plug-congₑ (M ∎) = (M ⟪ _ ⟫) ∎
plug-congₑ (M —→⟨ M→L ⟩ L↠N) = M ⟪ _ ⟫ —→⟨ ξ M→L ⟩ (plug-congₑ L↠N)

↠ₑ-trans : ∀ {L M N}
  → L —↠ₑ M
  → M —↠ₑ N
  → L —↠ₑ N
↠ₑ-trans (L ∎) (._ ∎) = L ∎
↠ₑ-trans (L ∎) (.L —→⟨ M→ ⟩ ↠N) = L —→⟨ M→ ⟩ ↠N
↠ₑ-trans (L —→⟨ L→ ⟩ ↠M) (M ∎) = L —→⟨ L→ ⟩ ↠M
↠ₑ-trans (L —→⟨ L→ ⟩ ↠M) (M —→⟨ M→ ⟩ ↠N) =
  L —→⟨ L→ ⟩ ↠ₑ-trans ↠M (M —→⟨ M→ ⟩ ↠N)

preserve-mult : ∀ {g} {M N} → ⊢ M ⇐ g → M —↠ₑ N → ⊢ N ⇐ g
preserve-mult ⊢M (_ ∎) = ⊢M
preserve-mult ⊢L (L —→⟨ L→M ⟩ M↠N) = preserve-mult (preserve ⊢L L→M) M↠N


data ⊢_⊑_⇐_⊑_ : ∀ (M M′ : LExpr) (g₁ g₂ : Label) → Set where

  ⊑-l : ∀ {ℓ} → ⊢ l ℓ ⊑ l ℓ ⇐ l ℓ ⊑ l ℓ

  ⊑-cast : ∀ {g₁ g₁′ g₂ g₂′} {M M′}
             {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ M ⊑ M′ ⇐ g₁ ⊑ g₁′
    → ⊢ c̅ ⊑ c̅′
      --------------------------------------
    → ⊢ M ⟪ c̅ ⟫ ⊑ M′ ⟪ c̅′ ⟫ ⇐ g₂ ⊑ g₂′

  ⊑-castl : ∀ {g₁ g₂ g′} {M M′} {c̅ : CExpr g₁ ⇒ g₂}
    → ⊢ M ⊑ M′ ⇐ g₁ ⊑ g′
    → ⊢l c̅ ⊑ g′
      --------------------------------------
    → ⊢ M ⟪ c̅ ⟫ ⊑ M′ ⇐ g₂ ⊑ g′

  ⊑-castr : ∀ {g g₁′ g₂′} {M M′} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ M ⊑ M′ ⇐ g ⊑ g₁′
    → ⊢r g ⊑ c̅′
      --------------------------------------
    → ⊢ M ⊑ M′ ⟪ c̅′ ⟫ ⇐ g ⊑ g₂′

  ⊑-blame : ∀ {g g′} {M} {p}
    → ⊢ M ⇐ g
    → g ⊑ₗ g′
      --------------------------
    → ⊢ M ⊑ blame p ⇐ g ⊑ g′


{- Precision implies that both sides are well-typed -}
prec→⊢ : ∀ {g g′} {M M′}
  → ⊢ M ⊑ M′ ⇐ g ⊑ g′
  → ⊢ M ⇐ g  ×  ⊢ M′ ⇐ g′
prec→⊢ ⊑-l = ⟨ ⊢l , ⊢l ⟩
prec→⊢ (⊑-cast M⊑M′ c̅⊑c̅′) =
  let ⟨ ⊢M , ⊢M′ ⟩ = prec→⊢ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢cast ⊢M′ ⟩
prec→⊢ (⊑-castl M⊑M′ _) =
  let ⟨ ⊢M , ⊢M′ ⟩ = prec→⊢ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢M′ ⟩
prec→⊢ (⊑-castr M⊑M′ _) =
  let ⟨ ⊢M , ⊢M′ ⟩ = prec→⊢ M⊑M′ in
  ⟨ ⊢M , ⊢cast ⊢M′ ⟩
prec→⊢ (⊑-blame ⊢M _) = ⟨ ⊢M , ⊢blame ⟩


{- Term precision implies type precision -}
prec→⊑ : ∀ {g₁ g₂} {M N} → ⊢ M ⊑ N ⇐ g₁ ⊑ g₂ → g₁ ⊑ₗ g₂
prec→⊑ ⊑-l = l⊑l
prec→⊑ (⊑-cast _ c̅⊑c̅′)   = proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)
prec→⊑ (⊑-castl _ c̅⊑g′)  = proj₂ (prec-left→⊑ _ c̅⊑g′)
prec→⊑ (⊑-castr _ g⊑c̅′)  = proj₂ (prec-right→⊑ _ g⊑c̅′)
prec→⊑ (⊑-blame ⊢M g⊑g′) = g⊑g′


{- Precision of label expressions implies the precision of coercion expressions -}
prec-inv : ∀ {ℓ ℓ′ g g′} {c̅ : CExpr l ℓ ⇒ g} {c̅′ : CExpr l ℓ′ ⇒ g′}
  → ⊢ l ℓ ⟪ c̅ ⟫ ⊑ l ℓ′ ⟪ c̅′ ⟫ ⇐ g ⊑ g′
  → ℓ ≡ ℓ′  ×  ⊢ c̅ ⊑ c̅′
prec-inv (⊑-cast ⊑-l c̅⊑c̅′)                 = ⟨ refl , c̅⊑c̅′ ⟩
prec-inv (⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) c̅⊑g′) = ⟨ refl , comp-pres-⊑-rl ℓ⊑c̅′ c̅⊑g′ ⟩
prec-inv (⊑-castr (⊑-castl ⊑-l c̅⊑ℓ) g⊑c̅′)  = ⟨ refl , comp-pres-⊑-lr c̅⊑ℓ g⊑c̅′  ⟩
