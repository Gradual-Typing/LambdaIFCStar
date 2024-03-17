module Dyn.ErasureSubstitution where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂)
open import Function using (case_of_)

open import Syntax

open import Common.Utils
open import Common.SecurityLabels
open import Memory.Addr
open import Dyn.Syntax
open import Dyn.Erasure


erase-σ : Subst → Subst
erase-σ σ = λ x → erase (σ x)

rename-erase : ∀ ρ M → erase (rename ρ M) ≡ rename ρ (erase M)
rename-erase ρ (` x) = refl
{- values -}
rename-erase ρ ($ k of low)  = refl
rename-erase ρ ($ k of high) = refl
rename-erase ρ (addr a⟦ low  ⟧ n of low)  = refl
rename-erase ρ (addr a⟦ low  ⟧ n of high) = refl
rename-erase ρ (addr a⟦ high ⟧ n of low)  = refl
rename-erase ρ (addr a⟦ high ⟧ n of high) = refl
rename-erase ρ (ƛ N of low)
  rewrite rename-erase (ext ρ) N = refl
rename-erase ρ (ƛ N of high) = refl
{- -- -}
rename-erase ρ (M · N)
  rewrite rename-erase ρ M | rename-erase ρ N = refl
rename-erase ρ (if L M N)
  rewrite rename-erase ρ L | rename-erase ρ M | rename-erase ρ N =
  refl
rename-erase ρ (ref?⟦ ℓ ⟧ M) rewrite rename-erase ρ M = refl
rename-erase ρ (! M) rewrite rename-erase ρ M = refl
rename-erase ρ (L :=? M)
  rewrite rename-erase ρ L | rename-erase ρ M = refl
rename-erase ρ ● = refl
rename-erase ρ (prot _ _) = refl

ext-erase : ∀ σ → ext (erase-σ σ) ≡ erase-σ (ext σ)
ext-erase σ = extensionality (ext-erase-x σ)
  where
  ext-erase-x : ∀ σ x → (ext (erase-σ σ)) x ≡ (erase-σ (ext σ)) x
  ext-erase-x σ zero = refl
  ext-erase-x σ (suc x) = sym goal
    where
    goal : erase (rename (↑ 1) (σ x)) ≡ rename (↑ 1) ((erase-σ σ) x)
    goal rewrite rename-erase (↑ 1) (σ x) = refl

subst-erase : ∀ σ M → erase (⟪ σ ⟫ M) ≡ ⟪ erase-σ σ ⟫ (erase M)
subst-erase σ (` x) = refl
{- values -}
subst-erase σ ($ k of low) = refl
subst-erase σ ($ k of high) = refl
subst-erase σ (addr a⟦ low ⟧ n of low) = refl
subst-erase σ (addr a⟦ low ⟧ n of high) = refl
subst-erase σ (addr a⟦ high ⟧ n of low) = refl
subst-erase σ (addr a⟦ high ⟧ n of high) = refl
subst-erase σ (ƛ N of low)
  rewrite subst-erase (ext σ) N | ext-erase σ = refl
subst-erase σ (ƛ N of high) = refl
{- -- -}
subst-erase σ (M · N)
  rewrite subst-erase σ M | subst-erase σ N = refl
subst-erase σ (if L M N)
  rewrite subst-erase σ L | subst-erase σ M | subst-erase σ N =
  refl
subst-erase σ (ref?⟦ ℓ ⟧ M) rewrite subst-erase σ M = refl
subst-erase σ (! M) rewrite subst-erase σ M = refl
subst-erase σ (L :=? M)
  rewrite subst-erase σ L | subst-erase σ M = refl
subst-erase σ ● = refl
subst-erase σ (prot _ _) = refl


subst-zero-erase : ∀ M → subst-zero (erase M) ≡ erase-σ (subst-zero M)
subst-zero-erase M = extensionality (subst-zero-erase-x M)
  where
  subst-zero-erase-x : ∀ M x → (subst-zero (erase M)) x ≡ (erase-σ (subst-zero M)) x
  subst-zero-erase-x M 0 = refl
  subst-zero-erase-x M (suc x) = refl

substitution-erase : ∀ N M → erase (N [ M ]) ≡ erase N [ erase M ]
substitution-erase N M rewrite subst-zero-erase M = subst-erase (subst-zero M) N
