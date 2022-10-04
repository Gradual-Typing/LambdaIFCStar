module ProxyElimination where

{- Destructing function and reference proxies by
   distributing casts into domain and co-domain -}

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import CCSyntax Cast_⇒_
open import CCTyping Cast_⇒_


{- NOTE:
   There are two types of inert function casts categorizing by gc₂:
     1) [ pc ] A → B of ℓ₁ ⇒ [ pc ] C → D of g₂
     2) [ pc ] A → B of ℓ₁ ⇒ [ ⋆  ] C → D of g₂
   -}
elim-fun-proxy : ∀ {A B C D gc₁ gc₂ g₁ g₂} {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
  → (V W : Term) → Inert c → (pc : StaticLabel) → Term
elim-fun-proxy V W (I-fun c I-label I-label) pc =
  case c of λ where
  (cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ l pc₂ ] C ⇒ D of g₂) p _) →
    (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
  (cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ ⋆ ] C ⇒ D of g₂) p _) →
    case pc ⋎ ℓ₁ ≼? pc₁ of λ where
    (yes _) → cast-pc (l pc) (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
    (no  _) → error (blame p)

{-
  Two types of inert reference casts categorizing by g₁:
    1) (S of ℓ₁) of ℓ ⇒ (T of ℓ₂) of g
    2) (S of ℓ₁) of ℓ ⇒ (T of ⋆ ) of g
-}
elim-ref-proxy : ∀ {A B g₁ g₂} {c : Cast Ref A of g₁ ⇒ Ref B of g₂}
  → (V M : Term) → Inert c → (_≔_ : Term → Term → Term) → Term
elim-ref-proxy V M (I-ref c I-label I-label) _≔_ =
  case c of λ where
  (cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of l ℓ₂) of g) p _) →
    V ≔ (M ⟨ in/c c ⟩)
  (cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of ⋆) of g) p _) →
    case ℓ ≼? ℓ₁ of λ where
    (yes _) → V ≔ (M ⟨ in/c c ⟩)
    (no  _) → error (blame p)
