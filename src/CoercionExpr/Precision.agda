module CoercionExpr.Precision where

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
open import CoercionExpr.CoercionExpr


infix 4 ⊢_⊑_
infix 4 ⊢l_⊑_
infix 4 ⊢r_⊑_

data ⊢_⊑_ : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CExpr g₁ ⇒ g₂) (c̅′ : CExpr g₁′ ⇒ g₂′) → Set where

  ⊑-id : ∀ {g g′}
    → (g⊑g′ : g ⊑ₗ g′)
      ---------------------------------
    → ⊢ id g ⊑ id g′

  ⊑-cast : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
             {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
             {c : ⊢ g₂ ⇒ g₃} {c′ : ⊢ g₂′ ⇒ g₃′}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₃′ {- c ⊑ c′ -}
      -------------------------------------------
    → ⊢ c̅ ⨾ c ⊑ c̅′ ⨾ c′

  ⊑-castl : ∀ {g₁ g₁′ g₂ g₂′ g₃}
              {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
              {c : ⊢ g₂ ⇒ g₃}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₃ ⊑ₗ g₂′  {- c ⊑ g₂′ -}
      -------------------------------------------
    → ⊢ c̅ ⨾ c ⊑ c̅′

  ⊑-castr : ∀ {g₁ g₁′ g₂ g₂′ g₃′}
              {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
              {c′ : ⊢ g₂′ ⇒ g₃′}
    → ⊢ c̅ ⊑ c̅′
    → g₂ ⊑ₗ g₂′ → g₂ ⊑ₗ g₃′  {- g₂ ⊑ c′ -}
      -------------------------------------------
    → ⊢ c̅ ⊑ c̅′ ⨾ c′

  ⊑-⊥ : ∀ {g₁ g₁′ g₂ g₂′} {c̅ : CExpr g₁ ⇒ g₂} {p}
    → g₁ ⊑ₗ g₁′
    → g₂ ⊑ₗ g₂′
      ---------------------------------
    → ⊢ c̅ ⊑ ⊥ g₁′ g₂′ p


data ⊢l_⊑_ : ∀ {g₁ g₂} (c̅ : CExpr g₁ ⇒ g₂) (g : Label) → Set where

  ⊑-id : ∀ {g g′}
    → (g⊑g′ : g ⊑ₗ g′)
      ---------------------------------
    → ⊢l id g ⊑ g′

  ⊑-cast : ∀ {g₁ g₂ g₃ g′}
             {c̅ : CExpr g₁ ⇒ g₂}
             {c : ⊢ g₂ ⇒ g₃}
    → ⊢l c̅ ⊑ g′
    → g₂ ⊑ₗ g′ → g₃ ⊑ₗ g′ {- c ⊑ g′ -}
      -------------------------------------------
    → ⊢l c̅ ⨾ c ⊑ g′


data ⊢r_⊑_ : ∀ {g₁′ g₂′} (g : Label) (c̅′ : CExpr g₁′ ⇒ g₂′) → Set where

  ⊑-id : ∀ {g g′}
    → (g⊑g′ : g ⊑ₗ g′)
      ---------------------------------
    → ⊢r g ⊑ id g′

  ⊑-cast : ∀ {g g₁′ g₂′ g₃′}
             {c̅′ : CExpr g₁′ ⇒ g₂′}
             {c′ : ⊢ g₂′ ⇒ g₃′}
    → ⊢r g ⊑ c̅′
    → g ⊑ₗ g₂′ → g ⊑ₗ g₃′ {- g ⊑ c′ -}
      -------------------------------------------
    → ⊢r g ⊑ c̅′ ⨾ c′

  ⊑-⊥ : ∀ {g g₁′ g₂′} {p}
    → g ⊑ₗ g₁′
    → g ⊑ₗ g₂′
      ---------------------------------
    → ⊢r g ⊑ ⊥ g₁′ g₂′ p


pres-prec-left : ∀ {g₁ g₂ g′} {c̅₁ c̅₂ : CExpr g₁ ⇒ g₂}
  → ⊢l c̅₁ ⊑ g′
  → c̅₁ —→ c̅₂
  → ⊢l c̅₂ ⊑ g′
pres-prec-left (⊑-cast prec g₁⊑g′ g₂⊑g′) (ξ r) =
  ⊑-cast (pres-prec-left prec r) g₁⊑g′ g₂⊑g′
pres-prec-left (⊑-cast () x x₁) ξ-⊥
pres-prec-left (⊑-cast prec _ _) (id x) = prec
pres-prec-left (⊑-cast (⊑-cast prec l⊑l ⋆⊑) ⋆⊑ l⊑l) (?-id x) = prec
pres-prec-left (⊑-cast (⊑-cast _ l⊑l ⋆⊑) ⋆⊑ ()) (?-↑ x)
pres-prec-left (⊑-cast (⊑-cast prec l⊑l ⋆⊑) ⋆⊑ ()) (?-⊥ x)

pres-prec-left-mult : ∀ {g₁ g₂ g′} {c̅₁ c̅₂ : CExpr g₁ ⇒ g₂}
  → ⊢l c̅₁ ⊑ g′
  → c̅₁ —↠ c̅₂
  → ⊢l c̅₂ ⊑ g′
pres-prec-left-mult prec (_ ∎) = prec
pres-prec-left-mult prec (_ —→⟨ r ⟩ r*) =
  let prec′ = pres-prec-left prec r in
  pres-prec-left-mult prec′ r*


prec→⊑ : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CExpr g₁ ⇒ g₂) (c̅′ : CExpr g₁′ ⇒ g₂′)
  → ⊢ c̅ ⊑ c̅′
  → (g₁ ⊑ₗ g₁′) × (g₂ ⊑ₗ g₂′)
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


prec-left→⊑ : ∀ {g₁ g₂ g′} (c̅ : CExpr g₁ ⇒ g₂)
  → ⊢l c̅ ⊑ g′
  → (g₁ ⊑ₗ g′) × (g₂ ⊑ₗ g′)
prec-left→⊑ (id g) (⊑-id g⊑g′) = ⟨ g⊑g′ , g⊑g′ ⟩
prec-left→⊑ (c̅ ⨾ c) (⊑-cast c̅⊑g′ g₁⊑g′ g₂⊑g′) =
  ⟨ proj₁ (prec-left→⊑ c̅ c̅⊑g′) , g₂⊑g′ ⟩

prec-right→⊑ : ∀ {g g₁′ g₂′} (c̅′ : CExpr g₁′ ⇒ g₂′)
  → ⊢r g ⊑ c̅′
  → (g ⊑ₗ g₁′) × (g ⊑ₗ g₂′)
prec-right→⊑ (id _) (⊑-id g⊑g′) = ⟨ g⊑g′ , g⊑g′ ⟩
prec-right→⊑ (_ ⨾ _) (⊑-cast g⊑c̅′ x y) = ⟨ proj₁ (prec-right→⊑ _ g⊑c̅′) , y ⟩
prec-right→⊑ (⊥ _ _ _) (⊑-⊥ x y) = ⟨ x , y ⟩

⊑-left-expand : ∀ {g₁ g₂ g′} {c̅ : CExpr g₁ ⇒ g₂}
  → ⊢l c̅ ⊑ g′
  → ⊢  c̅ ⊑ id g′
⊑-left-expand (⊑-id g⊑g′) = ⊑-id g⊑g′
⊑-left-expand (⊑-cast c̅⊑g′ g₁⊑g′ g₂⊑g′) = ⊑-castl (⊑-left-expand c̅⊑g′) g₁⊑g′ g₂⊑g′

⊑-left-contract : ∀ {g₁ g₂ g′} {c̅ : CExpr g₁ ⇒ g₂}
  → ⊢  c̅ ⊑ id g′
  → ⊢l c̅ ⊑ g′
⊑-left-contract (⊑-id g⊑g′) = ⊑-id g⊑g′
⊑-left-contract (⊑-castl c̅⊑id g₁⊑g′ g₂⊑g′) = ⊑-cast (⊑-left-contract c̅⊑id) g₁⊑g′ g₂⊑g′

⊑-right-expand : ∀ {g g₁′ g₂′} {c̅′ : CExpr g₁′ ⇒ g₂′}
  → ⊢r g ⊑ c̅′
  → ⊢  id g ⊑ c̅′
⊑-right-expand (⊑-id g⊑g′) = ⊑-id g⊑g′
⊑-right-expand (⊑-cast g⊑c̅′ g⊑g₁′ g⊑g₂′) = ⊑-castr (⊑-right-expand g⊑c̅′) g⊑g₁′ g⊑g₂′
⊑-right-expand (⊑-⊥ g⊑g₁′ g⊑g₂′) = ⊑-⊥ g⊑g₁′ g⊑g₂′

⊑-right-contract : ∀ {g g₁′ g₂′} {c̅′ : CExpr g₁′ ⇒ g₂′}
  → ⊢ id g ⊑ c̅′
  → ⊢r   g ⊑ c̅′
⊑-right-contract (⊑-id g⊑g′) = ⊑-id g⊑g′
⊑-right-contract (⊑-castr id⊑c̅′ g⊑g₁′ g⊑g₂′) = ⊑-cast (⊑-right-contract id⊑c̅′) g⊑g₁′ g⊑g₂′
⊑-right-contract (⊑-⊥ g⊑g₁′ g⊑g₂′) = ⊑-⊥ g⊑g₁′ g⊑g₂′


prec-inj-left : ∀ {g g′ ℓ}
  (c̅ₙ : CExpr g ⇒ ⋆) (c̅ₙ′ : CExpr g′ ⇒ l ℓ)
  → CVal c̅ₙ → CVal c̅ₙ′
  → ⊢ c̅ₙ ⊑ c̅ₙ′ ⨾ ℓ !
  → ⊢ c̅ₙ ⊑ c̅ₙ′
prec-inj-left (c̅ₙ ⨾ c) c̅ₙ′ v v′ (⊑-cast c̅ₙ⊑c̅ₙ′ g₁⊑ℓ ⋆⊑) = ⊑-castl c̅ₙ⊑c̅ₙ′ g₁⊑ℓ ⋆⊑
prec-inj-left (c̅ₙ ⨾ id .⋆) c̅ₙ′ () v′ (⊑-castl c̅ₙ⊑c̅ₙ′⨾! ⋆⊑ ⋆⊑)
prec-inj-left c̅ₙ c̅ₙ′ v v′ (⊑-castr c̅ₙ⊑c̅ₙ′⨾! ⋆⊑ ⋆⊑) = c̅ₙ⊑c̅ₙ′⨾!
