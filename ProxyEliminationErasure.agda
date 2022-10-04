module ProxyEliminationErasure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import CC
open import WellTyped

open import Erasure

elim-fun-proxy-erase : ∀ {A B C D gc₁ gc₂ g₁ g₂} {M}
  → ∀ {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
  → ∀ V W (i : Inert c) pc
  → M ≡ elim-fun-proxy V W i pc
  → ¬ Err M
    ----------------------------------------------------
  → erase M ≡ erase (V · W)
elim-fun-proxy-erase V W (I-fun c I-label I-label) pc refl ¬err with c
... | cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ l pc₂ ] C ⇒ D of g₂) p _ = refl
... | cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ ⋆     ] C ⇒ D of g₂) p _
  with pc ⋎ ℓ₁ ≼? pc₁
...   | yes _ = refl
...   | no  _ = contradiction E-error ¬err

elim-ref-proxy-erase : ∀ {A B g₁ g₂} {N} {_≔_}
  → ∀ {c : Cast Ref A of g₁ ⇒ Ref B of g₂}
  → ∀ V M (i : Inert c)
  → RefAssign _≔_
  → N ≡ elim-ref-proxy V M i _≔_
  → ¬ Err N
    ----------------------------------------------------
  → erase N ≡ erase (V ≔ M)
elim-ref-proxy-erase V M (I-ref c I-label I-label) static refl ¬err with c
... | cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of l ℓ₂) of g) p _ = refl
... | cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of ⋆   ) of g) p _
  with ℓ ≼? ℓ₁
...   | yes _ = refl
...   | no  _ = contradiction E-error ¬err
elim-ref-proxy-erase V M (I-ref c I-label I-label) checked refl ¬err with c
... | cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of l ℓ₂) of g) p _ = refl
... | cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of ⋆   ) of g) p _
  with ℓ ≼? ℓ₁
...   | yes _ = refl
...   | no  _ = contradiction E-error ¬err
elim-ref-proxy-erase V M (I-ref c I-label I-label) unchecked refl ¬err with c
... | cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of l ℓ₂) of g) p _ = refl
... | cast (Ref (S of l ℓ₁) of l ℓ) (Ref (T of ⋆   ) of g) p _
  with ℓ ≼? ℓ₁
...   | yes _ = refl
...   | no  _ = contradiction E-error ¬err
