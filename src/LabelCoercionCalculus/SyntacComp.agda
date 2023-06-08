{- Syntactical composition of coercion expressions -}

module LabelCoercionCalculus.SyntacComp where

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
open import LabelCoercionCalculus.CoercionExp
open import LabelCoercionCalculus.Precision


_⨟_ : ∀ {g₁ g₂ g₃} (c̅₁ : CoercionExp g₁ ⇒ g₂) (c̅₂ : CoercionExp g₂ ⇒ g₃) → CoercionExp g₁ ⇒ g₃
c̅₁ ⨟ ⊥ g₂ g₃ p = ⊥ _ g₃ p
c̅₁ ⨟ id g      = c̅₁ ⨾ id g
c̅₁ ⨟ (c̅₂ ⨾ c)  = (c̅₁ ⨟ c̅₂) ⨾ c


comp-pres-prec : ∀ {g₁ g₁′ g₂ g₂′ g₃ g₃′}
     {c̅₁ : CoercionExp g₁ ⇒ g₂}    {c̅₂ : CoercionExp g₂ ⇒ g₃}
     {c̅₁′ : CoercionExp g₁′ ⇒ g₂′} {c̅₂′ : CoercionExp g₂′ ⇒ g₃′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → ⊢ c̅₂ ⊑ c̅₂′
    -----------------------------
  → ⊢ c̅₁ ⨟ c̅₂ ⊑ c̅₁′ ⨟ c̅₂′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-⊥ x g₃⊑g₃′) =
  let ⟨ g₁⊑g₁′ , _ ⟩ = prec→⊑ _ _ c̅₁⊑c̅₁′ in
  ⊑-⊥ g₁⊑g₁′ g₃⊑g₃′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-id g⊑g′) = ⊑-cast c̅₁⊑c̅₁′ g⊑g′ g⊑g′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-cast c̅₂⊑c̅₂′ g⊑g₃ g′⊑g₃′) =
  ⊑-cast (comp-pres-prec c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g⊑g₃ g′⊑g₃′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-castl c̅₂⊑c̅₂′ g⊑g₃′ g₃⊑g₃′) =
  ⊑-castl (comp-pres-prec c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g⊑g₃′ g₃⊑g₃′
comp-pres-prec c̅₁⊑c̅₁′ (⊑-castr c̅₂⊑c̅₂′ g₃⊑g′ g₃⊑g₃′) =
  ⊑-castr (comp-pres-prec c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g₃⊑g′ g₃⊑g₃′


comp-pres-⊑-ll : ∀ {g₁ g₂ g₃ g′}
     {c̅₁ : CoercionExp g₁ ⇒ g₂}    {c̅₂ : CoercionExp g₂ ⇒ g₃}
  → ⊢l c̅₁ ⊑ g′
  → ⊢l c̅₂ ⊑ g′
    -----------------------------
  → ⊢l c̅₁ ⨟ c̅₂ ⊑ g′
comp-pres-⊑-ll c̅₁⊑c̅₁′ (⊑-id g⊑g′) = ⊑-cast c̅₁⊑c̅₁′ g⊑g′ g⊑g′
comp-pres-⊑-ll c̅₁⊑c̅₁′ (⊑-cast c̅₂⊑c̅₂′ g⊑g₃′ g₃⊑g₃′) =
  ⊑-cast (comp-pres-⊑-ll c̅₁⊑c̅₁′ c̅₂⊑c̅₂′) g⊑g₃′ g₃⊑g₃′

comp-pres-⊑-lr : ∀ {g₁ g₁′ g₂ g₂′}
     {c̅ : CoercionExp g₁ ⇒ g₂}    {c̅′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢l c̅ ⊑ g₁′
  → ⊢r g₂ ⊑ c̅′
    -----------------------------
  → ⊢ c̅ ⊑ c̅′
comp-pres-⊑-lr c̅⊑g₁′ (⊑-id g⊑g′) = ⊑-left-expand c̅⊑g₁′
comp-pres-⊑-lr c̅⊑g₁′ (⊑-cast g₂⊑c̅′ x y) = ⊑-castr (comp-pres-⊑-lr c̅⊑g₁′ g₂⊑c̅′) x y
comp-pres-⊑-lr c̅⊑g₁′ (⊑-⊥ x y) = ⊑-⊥ (proj₁ (prec-left→⊑ _ c̅⊑g₁′)) y

comp-pres-⊑-rl : ∀ {g₁ g₁′ g₂ g₂′}
     {c̅ : CoercionExp g₁ ⇒ g₂}    {c̅′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢r g₁ ⊑ c̅′
  → ⊢l c̅ ⊑ g₂′
    -----------------------------
  → ⊢ c̅ ⊑ c̅′
comp-pres-⊑-rl g₁⊑c̅′ (⊑-id g⊑g′) = ⊑-right-expand g₁⊑c̅′
comp-pres-⊑-rl g₁⊑c̅′ (⊑-cast c̅⊑g₂′ g₁⊑g₂′ g₂⊑g₂′) = ⊑-castl (comp-pres-⊑-rl g₁⊑c̅′ c̅⊑g₂′) g₁⊑g₂′ g₂⊑g₂′

comp-pres-⊑-lb : ∀ {g₁ g₁′ g₂ g₂′ g₃}
     {c̅₁ : CoercionExp g₁ ⇒ g₂}    {c̅₂ : CoercionExp g₂ ⇒ g₃}
     {c̅′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢l c̅₁ ⊑ g₁′
  → ⊢  c̅₂ ⊑ c̅′
    -----------------------------
  → ⊢ c̅₁ ⨟ c̅₂ ⊑ c̅′
comp-pres-⊑-lb c̅₁⊑g₁ (⊑-id g⊑g′) = ⊑-castl (⊑-left-expand c̅₁⊑g₁) g⊑g′ g⊑g′
comp-pres-⊑-lb c̅₁⊑g₁ (⊑-cast c̅⊑c̅′ g₁⊑g₁′ g₂⊑g₂′) = ⊑-cast (comp-pres-⊑-lb c̅₁⊑g₁ c̅⊑c̅′) g₁⊑g₁′ g₂⊑g₂′
comp-pres-⊑-lb c̅₁⊑g₁ (⊑-castl c̅⊑c̅′ g₁⊑g′ g₂⊑g′) = ⊑-castl (comp-pres-⊑-lb c̅₁⊑g₁ c̅⊑c̅′) g₁⊑g′ g₂⊑g′
comp-pres-⊑-lb c̅₁⊑g₁ (⊑-castr c̅⊑c̅′ g⊑g₁′ g⊑g₂′) = ⊑-castr (comp-pres-⊑-lb c̅₁⊑g₁ c̅⊑c̅′) g⊑g₁′ g⊑g₂′
comp-pres-⊑-lb c̅₁⊑g₁ (⊑-⊥ g₁⊑g₁′ g₂⊑g₂′) = ⊑-⊥ (proj₁ (prec-left→⊑ _ c̅₁⊑g₁)) g₂⊑g₂′

comp-pres-⊑-bl : ∀ {g₁ g₁′ g₂ g₂′ g₃}
     {c̅₁ : CoercionExp g₁ ⇒ g₂}    {c̅₂ : CoercionExp g₂ ⇒ g₃}
     {c̅′ : CoercionExp g₁′ ⇒ g₂′}
  → ⊢  c̅₁ ⊑ c̅′
  → ⊢l c̅₂ ⊑ g₂′
    -----------------------------
  → ⊢ c̅₁ ⨟ c̅₂ ⊑ c̅′
comp-pres-⊑-bl c̅₁⊑c̅′ (⊑-id g⊑g′) = ⊑-castl c̅₁⊑c̅′ g⊑g′ g⊑g′
comp-pres-⊑-bl c̅₁⊑c̅′ (⊑-cast c̅₂⊑g₂′ g₁⊑g₂′ g₂⊑g₂′) =
  ⊑-castl (comp-pres-⊑-bl c̅₁⊑c̅′ c̅₂⊑g₂′) g₁⊑g₂′ g₂⊑g₂′
