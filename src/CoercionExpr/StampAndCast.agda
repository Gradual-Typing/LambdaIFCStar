module CoercionExpr.StampAndCast where

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
open import CoercionExpr.Precision
open import CoercionExpr.SyntacComp
open import CoercionExpr.Stamping


stamp-and-cast : ∀ {ℓ₁ g₁ g₂} (c̅ₙ : CExpr l ℓ₁ ⇒ g₁)
  → CVal c̅ₙ
  → (ℓ₂ : StaticLabel)
  → g₁ ⋎̃ l ℓ₂ ≾ g₂
  → NotProj (g₁ ⋎̃ l ℓ₂) g₂
  → CExpr l ℓ₁ ⇒ g₂
stamp-and-cast {ℓ₁} {g₁} {g₂} c̅ₙ v ℓ₂ lp np =
  stampₗ c̅ₙ v ℓ₂ ⨾ coerce-nproj (g₁ ⋎̃ l ℓ₂) g₂ lp np

stamp-cast-prec : ∀ {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′ g₁ g₁′ g₂ g₂′}
     {np : NotProj (g₁ ⋎̃ l ℓ₂) g₂} {np′ : NotProj (g₁′ ⋎̃ l ℓ₂′) g₂′}
     {c̅ₙ : CExpr l ℓ₁ ⇒ g₁} {c̅ₙ′ : CExpr l ℓ₁′ ⇒ g₁′}
  → (v : CVal c̅ₙ) → (v′ : CVal c̅ₙ′)
  → (c~ : g₁ ⋎̃ l ℓ₂ ≾ g₂) → (c~′ : g₁′ ⋎̃ l ℓ₂′ ≾ g₂′)
  → ⊢ c̅ₙ ⊑ c̅ₙ′
  → g₂ ⊑ₗ g₂′
  → ℓ₂ ≼ ℓ₂′
    ------------------------------------------------------------------------
  → ⊢ stamp-and-cast c̅ₙ v ℓ₂ c~ np ⊑ stamp-and-cast c̅ₙ′ v′ ℓ₂′ c~′ np′
{- stamping low on both sides -}
stamp-cast-prec {g₁ = g₁} {g₁′} v v′ c~ c~′ prec g⊑g′ l≼l
  rewrite g⋎̃low≡g {g₁} | g⋎̃low≡g {g₁′} = ⊑-cast prec (proj₂ (prec→⊑ _ _ prec)) g⊑g′
{- stamping high on both sides -}
stamp-cast-prec {low}  id id c~ c~′ (⊑-id l⊑l) g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l g⊑g′
stamp-cast-prec {high} id id c~ c~′ (⊑-id l⊑l) g⊑g′ h≼h =
  ⊑-cast (⊑-id l⊑l) l⊑l g⊑g′
stamp-cast-prec id (inj id) c~ c~′ (⊑-castr _ _ ()) g⊑g′ h≼h
stamp-cast-prec id (inj (up v′)) c~ c~′ (⊑-castr _ _ ()) g⊑g′ h≼h
stamp-cast-prec id (up v′) c~ c~′ (⊑-castr _ l⊑l ()) g⊑g′ h≼h
stamp-cast-prec {low}  (inj id) id c~ c~′ (⊑-castl (⊑-id l⊑l) _ _) g⊑g′ h≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {high} (inj id) id c~ c~′ (⊑-castl (⊑-id l⊑l) _ _) g⊑g′ h≼h =
  ⊑-cast (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up v)) id c~ c~′ (⊑-castl (⊑-castl _ l⊑l ()) _ _) g⊑g′ h≼h
stamp-cast-prec {low}  (inj id) (inj id) c~ c~′ (⊑-cast _ l⊑l _) g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {high} (inj id) (inj id) c~ c~′ (⊑-cast _ l⊑l _) g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {low}  (inj id) (inj id) c~ c~′ (⊑-castr (⊑-castl _ l⊑l _) _ _) g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {high} (inj id) (inj id) c~ c~′ (⊑-castr (⊑-castl _ l⊑l _) _ _) g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (inj (up v′)) c~ c~′ (⊑-cast (⊑-castr _ l⊑l ()) _ _) g⊑g′ h≼h
stamp-cast-prec (inj id) (inj (up id)) c~ c~′ (⊑-castr (⊑-cast _ l⊑l _) _ _) g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (inj (up v′)) c~ c~′ (⊑-castr (⊑-castl (⊑-castr _ l⊑l ()) _ _) _ _) g⊑g′ h≼h
stamp-cast-prec (inj id) (inj (up id)) c~ c~′ (⊑-castr (⊑-castr (⊑-castl _ l⊑l _) _ _) _ _) g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (inj id) c~ c~′ (⊑-cast (⊑-castl _ l⊑l ()) _ _) g⊑g′ h≼h
stamp-cast-prec (inj (up id)) (inj id) c~ c~′ (⊑-castr (⊑-castl (⊑-castl _ l⊑l ()) _ _) _ _) g⊑g′ h≼h
stamp-cast-prec (inj (up id)) (inj (up id)) c~ c~′ prec g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (up id) c~ c~′ (⊑-cast _ l⊑l _) g⊑g′ h≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (up id) c~ c~′ (⊑-castl (⊑-castr _ () _) l⊑l _) g⊑g′ h≼h
stamp-cast-prec (inj id) (up id) c~ c~′ (⊑-castr (⊑-castl _ l⊑l _) _ _) g⊑g′ h≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (up id) c~ c~′ prec g⊑g′ h≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (up id) id c~ c~′ (⊑-castl _ l⊑l ()) g⊑g′ h≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-cast _ _ ()) g⊑g′ h≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-castl _ () _) g⊑g′ h≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-castr _ _ ()) g⊑g′ h≼h
stamp-cast-prec (up id) (inj (up id)) c~ c~′ (⊑-cast _ _ ()) g⊑g′ h≼h
stamp-cast-prec (up id) (inj (up id)) c~ c~′ (⊑-castl _ _ ()) g⊑g′ h≼h
stamp-cast-prec (up id) (inj (up id)) c~ c~′ (⊑-castr _ _ ()) g⊑g′ h≼h
stamp-cast-prec (up id) (up id) c~ c~′ prec g⊑g′ h≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l g⊑g′
{- stamping low on less precise and high on more precise side -}
stamp-cast-prec {low}  id id c~ c~′ (⊑-id l⊑l) ⋆⊑ l≼h =
  ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑
stamp-cast-prec {high} id id c~ c~′ (⊑-id l⊑l) ⋆⊑ l≼h =
  ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp-cast-prec {low} id id c~ (≾-l h≼h) (⊑-id l⊑l) l⊑l l≼h =
  ⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l l⊑l
stamp-cast-prec {high} id id c~ c~′ (⊑-id l⊑l) l⊑l l≼h =
  ⊑-cast (⊑-id l⊑l) l⊑l l⊑l
stamp-cast-prec id (inj id) c~ c~′ (⊑-castr _ _ ()) g⊑g′ l≼h
stamp-cast-prec id (inj (up id)) c~ c~′
                (⊑-castr (⊑-castr (⊑-id l⊑l) _ ()) _ _) g⊑g′ l≼h
stamp-cast-prec id (up id) c~ c~′
                (⊑-castr (⊑-id l⊑l) x ()) g⊑g′ l≼h
stamp-cast-prec {ℓ} (inj id) id c~ c~′
                (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h with ℓ
... | low  = ⊑-cast (⊑-cast  (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
... | high = ⊑-cast (⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {low}  (inj id) (inj id) c~ c~′
                       (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {high} (inj id) (inj id) c~ c~′
                       (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast  (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {low}  (inj id) (inj id) c~ c~′
                       (⊑-castr (⊑-castl _ l⊑l ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec {high} (inj id) (inj id) c~ c~′
                       (⊑-castr (⊑-castl _ l⊑l ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast  (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
                (⊑-cast (⊑-castr (⊑-id ()) x x₁) l⊑l _) g⊑g′ l≼h
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
                (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
                (⊑-castr (⊑-castl (⊑-castr _ l⊑l ()) _ _) _ _) g⊑g′ l≼h
stamp-cast-prec (inj id) (inj (up id)) c~ c~′
    (⊑-castr (⊑-castr (⊑-castl _ l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-castr (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (up id) c~ c~′ (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj id) (up id) c~ c~′
                (⊑-castl (⊑-castr _ () _) l⊑l ⋆⊑) g⊑g′ l≼h
stamp-cast-prec (inj id) (up id) c~ c~′ (⊑-castr (⊑-castl _ l⊑l x₃) x x₁) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) id c~ c~′
                (⊑-castl (⊑-castl (⊑-id l⊑l) _ ()) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (inj id) c~ c~′
                (⊑-cast (⊑-castl (⊑-id l⊑l) _ ()) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (inj id) c~ c~′
                (⊑-castr (⊑-castl (⊑-castl (⊑-id l⊑l) _ ()) _ _) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (inj (up id)) c~ c~′
                (⊑-cast (⊑-cast _ l⊑l l⊑l) l⊑l ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (inj (up id)) c~ c~′
                (⊑-castr (⊑-castl _ l⊑l ⋆⊑) ⋆⊑ ⋆⊑) g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (inj (up id)) c~ c~′
                (⊑-castr (⊑-castr (⊑-castl _ () _) _ _) _ _) g⊑g′ l≼h
stamp-cast-prec (inj (up id)) (up id) c~ c~′ (⊑-castl _ _ _) g⊑g′ l≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (inj (up id)) (up id) c~ c~′ (⊑-castr _ _ _) g⊑g′ l≼h =
  ⊑-cast (⊑-castl (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l ⋆⊑) ⋆⊑ g⊑g′
stamp-cast-prec (up id) id c~ c~′ (⊑-castl (⊑-id l⊑l) _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-cast (⊑-id _) _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-castl _ () _) g⊑g′ l≼h
stamp-cast-prec (up id) (inj id) c~ c~′ (⊑-castr _ _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj (up v′)) c~ c~′ (⊑-cast _ _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (inj (up v′)) c~ c~′ (⊑-castl _ () _) g⊑g′ l≼h
stamp-cast-prec (up id) (inj (up v′)) c~ c~′ (⊑-castr _ _ ()) g⊑g′ l≼h
stamp-cast-prec (up id) (up id) c~ c~′ prec g⊑g′ l≼h =
  ⊑-cast (⊑-cast (⊑-id l⊑l) l⊑l l⊑l) l⊑l g⊑g′
