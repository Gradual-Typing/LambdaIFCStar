module Dyn.BigStepSimulation where

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

open import Common.Utils
open import Common.Types using (Base; rep)
open import Common.SecurityLabels
open import Dyn.Syntax
open import Dyn.Values
open import Dyn.BigStep
open import Dyn.BigStepErased
open import Dyn.Erasure
open import Dyn.HeapSecure
open import Dyn.ErasureSubstitution public


sim : ∀ {pc M V μ μ′}
  → μ ∣ pc ⊢ M ⇓ V ∣ μ′
    ----------------------------------------------------------------------------------
  → erase-μ μ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
sim (⇓-val v) = (⇓ₑ-val (erase-val-value v))
sim {pc} {μ′ = μ′} (⇓-app {L = L} {M} {N} {V} {W} {ℓ = ℓ} L⇓ƛN M⇓V N[V]⇓W) with ℓ
... | low rewrite stamp-val-low (⇓-value N[V]⇓W) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-app (sim L⇓ƛN) (sim M⇓V) ϵN[ϵV]⇓ϵW
  where
  ϵN[ϵV]⇓ϵW : _ ∣ pc ⊢ erase N [ erase V ] ⇓ₑ erase W ∣ _
  ϵN[ϵV]⇓ϵW rewrite sym (substitution-erase N V) = sim N[V]⇓W
... | high rewrite erase-stamp-high (⇓-value N[V]⇓W) | ℓ⋎high≡high {pc} =
  ⇓ₑ-app-● (sim L⇓ƛN) ϵM⇓ϵV
  where
  ϵμ₂≡ϵμ′ = heap-relate N[V]⇓W
  ϵM⇓ϵV : _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
  ϵM⇓ϵV = subst (λ □ → _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ □)
             ϵμ₂≡ϵμ′ (sim M⇓V)
sim {pc} {μ = μ} {μ′} (⇓-if-true  {μ₁ = μ₁} {L = L} {M} {N} {V} {ℓ = ℓ} L⇓true  M⇓V)
  with ℓ
... | low  rewrite stamp-val-low (⇓-value M⇓V) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-if-true (sim L⇓true) (sim M⇓V)
... | high rewrite erase-stamp-high (⇓-value M⇓V) | ℓ⋎high≡high {pc} =
  ⇓ₑ-if-● ϵL⇓●
  where
  ϵμ₁≡ϵμ′ : erase-μ μ₁ ≡ erase-μ μ′
  ϵμ₁≡ϵμ′ = heap-relate M⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ′
  ϵL⇓● rewrite sym ϵμ₁≡ϵμ′ = sim L⇓true
sim {pc} {μ = μ} {μ′} (⇓-if-false {μ₁ = μ₁} {L = L} {M} {N} {V} {ℓ = ℓ} L⇓false  N⇓V)
  with ℓ
... | low  rewrite stamp-val-low (⇓-value N⇓V) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-if-false (sim L⇓false) (sim N⇓V)
... | high rewrite erase-stamp-high (⇓-value N⇓V) | ℓ⋎high≡high {pc} =
  ⇓ₑ-if-● ϵL⇓●
  where
  ϵμ₁≡ϵμ′ : erase-μ μ₁ ≡ erase-μ μ′
  ϵμ₁≡ϵμ′ = heap-relate N⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ′
  ϵL⇓● rewrite sym ϵμ₁≡ϵμ′ = sim L⇓false
sim (⇓-ref? {μ} {μ₁} {M = M} {V} {ℓ = low} M⇓V fresh pc≼ℓ)
  rewrite erase-μᴸ-length (proj₁ μ₁) =
  ⇓ₑ-ref? goal fresh pc≼ℓ
  where
  goal : erase-μᴸ (proj₁ μ) ∣ _ ⊢ erase M ⇓ₑ
      erase (stamp-val V (⇓-value M⇓V) low) ∣ erase-μᴸ (proj₁ μ₁)
  goal rewrite stamp-val-low (⇓-value M⇓V) = sim M⇓V
sim (⇓-ref? {ℓ = high} M⇓V fresh pc≼ℓ) =
  ⇓ₑ-ref?-● (sim M⇓V)
sim {μ′ = ⟨ μᴸ , μᴴ ⟩} (⇓-deref {v = v} {n = n} {ℓ = low} {low} M⇓a eq)
  rewrite stamp-val-low v =
  ⇓ₑ-deref {v = erase-val-value v} (sim M⇓a)
    (erase-μ-lookup-low {μᴸ} {μᴴ} {n} {v = v} eq)
sim (⇓-deref {v = v} {ℓ = low} {high} M⇓a eq)
  rewrite erase-stamp-high v = {!!} -- ⇓ₑ-deref-● (sim M⇓a)
sim (⇓-deref {v = v} {ℓ = high} {low} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim M⇓a)
sim (⇓-deref {v = v} {ℓ = high} {high} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim M⇓a)
sim {pc = pc} (⇓-assign? {L = L} {M} {V} {ℓ = ℓ} {ℓ₁} L⇓a M⇓V pc⋎ℓ≼ℓ₁)
  with ℓ | ℓ₁
...   | low | low =
  ⇓ₑ-assign? (sim L⇓a) goal pc⋎ℓ≼ℓ₁
  where
  goal : erase-μᴸ _ ∣ _ ⊢ erase M ⇓ₑ
      erase (stamp-val V (⇓-value M⇓V) low) ∣ erase-μᴸ _
  goal rewrite stamp-val-low (⇓-value M⇓V) = sim M⇓V
...   | low | high =
  ⇓ₑ-assign?-● (sim L⇓a) (sim M⇓V)
...   | high | high =
  ⇓ₑ-assign?-● (sim L⇓a) (sim M⇓V)
...   | high | low with pc
...   | low  = case pc⋎ℓ≼ℓ₁ of λ where ()
...   | high = case pc⋎ℓ≼ℓ₁ of λ where ()
