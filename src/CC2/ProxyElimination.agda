module CC2.ProxyElimination where

{- Destructing function and reference proxies by
   distributing casts into domain and co-domain -}

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Function using (case_of_)

open import Common.Types
open import Common.TypeBasedCast
open import CC.CCSyntax Cast_⇒_
open import CC2.CCTyping Cast_⇒_


{- NOTE:
   There are two types of inert function casts categorizing by gc₂:
     1) [ pc ] A → B of ℓ₁ ⇒ [ pc ] C → D of g₂
     2) [ pc ] A → B of ℓ₁ ⇒ [ ⋆  ] C → D of g₂
   -}
elim-fun-proxy : ∀ {A B C D gc₁ gc₂ g₁ g₂} {c : Cast (⟦ gc₁ ⟧ A ⇒ B of g₁) ⇒ (⟦ gc₂ ⟧ C ⇒ D of g₂)}
  → (V W : Term) → Inert c → (pc : StaticLabel) → Term
elim-fun-proxy V W (I-fun c I-label I-label) pc =
  case c of λ where
  (cast (⟦ l pc₁ ⟧ A ⇒ B of l ℓ₁) (⟦ l pc₂ ⟧ C ⇒ D of g₂) p _) →
    (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
  (cast (⟦ l pc₁ ⟧ A ⇒ B of l ℓ₁) (⟦ ⋆ ⟧ C ⇒ D of g₂) p _) →
    case pc ⋎ ℓ₁ ≼? pc₁ of λ where
    (yes _) → cast-pc (l pc) (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
    (no  _) → error (blame p)

elim-ref-proxy : ∀ {A T g} {c : Cast Ref A of g ⇒ Ref (T of ⋆) of ⋆}
  → (V M : Term) → Inert c → (pc : StaticLabel) → Term
elim-ref-proxy V M (I-ref c I-label I-label) pc with c
... | (cast (Ref (S of l ℓ̂) of l ℓ) (Ref (T of ⋆) of g) p _) =
  case ⟨ ℓ ≼? ℓ̂ , pc ≼? ℓ̂ ⟩ of λ where
  ⟨ yes _ , yes _ ⟩ → V :=✓ (M ⟨ in/c c ⟩)
  ⟨ _ , _ ⟩ → error (blame p)   {- TODO: fix the blame label -}
