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
  → Secure μ
  → μ ∣ pc ⊢ M ⇓ V ∣ μ′
    ----------------------------------------------------------------------------------
  → erase-μ μ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
sim sec (⇓-val v) = (⇓ₑ-val (erase-val-value v))
sim {pc} {μ′ = μ′} sec (⇓-app {L = L} {M} {N} {V} {W} {ℓ = ℓ} L⇓ƛN M⇓V N[V]⇓W) with ℓ
... | low rewrite stamp-val-low (⇓-value N[V]⇓W) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-app (sim sec L⇓ƛN) (sim (⇓-pres-sec sec L⇓ƛN) M⇓V) ϵN[ϵV]⇓ϵW
  where
  ϵN[ϵV]⇓ϵW : _ ∣ pc ⊢ erase N [ erase V ] ⇓ₑ erase W ∣ _
  ϵN[ϵV]⇓ϵW rewrite sym (substitution-erase N V) =
    sim (⇓-pres-sec (⇓-pres-sec sec L⇓ƛN) M⇓V) N[V]⇓W
... | high rewrite erase-stamp-high (⇓-value N[V]⇓W) | ℓ⋎high≡high {pc} =
  ⇓ₑ-app-● (sim sec L⇓ƛN) ϵM⇓ϵV
  where
  ϵμ₂≡ϵμ′ = heap-relate N[V]⇓W
  ϵM⇓ϵV : _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
  ϵM⇓ϵV = subst (λ □ → _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ □)
             ϵμ₂≡ϵμ′ (sim (⇓-pres-sec sec L⇓ƛN) M⇓V)
sim {pc} {μ = μ} {μ′} sec (⇓-if-true  {μ₁ = μ₁} {L = L} {M} {N} {V} {ℓ = ℓ} L⇓true  M⇓V)
  with ℓ
... | low  rewrite stamp-val-low (⇓-value M⇓V) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-if-true (sim sec L⇓true) (sim (⇓-pres-sec sec L⇓true) M⇓V)
... | high rewrite erase-stamp-high (⇓-value M⇓V) | ℓ⋎high≡high {pc} =
  ⇓ₑ-if-● ϵL⇓●
  where
  ϵμ₁≡ϵμ′ : erase-μ μ₁ ≡ erase-μ μ′
  ϵμ₁≡ϵμ′ = heap-relate M⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ′
  ϵL⇓● rewrite sym ϵμ₁≡ϵμ′ = sim sec L⇓true
sim {pc} {μ = μ} {μ′} sec (⇓-if-false {μ₁ = μ₁} {L = L} {M} {N} {V} {ℓ = ℓ} L⇓false  N⇓V)
  with ℓ
... | low  rewrite stamp-val-low (⇓-value N⇓V) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-if-false (sim sec L⇓false) (sim (⇓-pres-sec sec L⇓false) N⇓V)
... | high rewrite erase-stamp-high (⇓-value N⇓V) | ℓ⋎high≡high {pc} =
  ⇓ₑ-if-● ϵL⇓●
  where
  ϵμ₁≡ϵμ′ : erase-μ μ₁ ≡ erase-μ μ′
  ϵμ₁≡ϵμ′ = heap-relate N⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ′
  ϵL⇓● rewrite sym ϵμ₁≡ϵμ′ = sim sec L⇓false
sim sec (⇓-ref? {μ} {μ₁} {M = M} {V} {ℓ = low} M⇓V fresh pc≼ℓ)
  rewrite erase-μᴸ-length (proj₁ μ₁) =
  ⇓ₑ-ref? goal fresh pc≼ℓ
  where
  goal : erase-μᴸ (proj₁ μ) ∣ _ ⊢ erase M ⇓ₑ
      erase (stamp-val V (⇓-value M⇓V) low) ∣ erase-μᴸ (proj₁ μ₁)
  goal rewrite stamp-val-low (⇓-value M⇓V) = sim sec M⇓V
sim sec (⇓-ref? {ℓ = high} M⇓V fresh pc≼ℓ) =
  ⇓ₑ-ref?-● (sim sec M⇓V)
sim {μ′ = ⟨ μᴸ , μᴴ ⟩} sec (⇓-deref {v = v} {n = n} {ℓ = low} {low} M⇓a eq)
  rewrite stamp-val-low v =
  ⇓ₑ-deref {v = erase-val-value v} (sim sec M⇓a)
    (erase-μ-lookup-low {μᴸ} {μᴴ} {n} {v = v} eq)
sim sec (⇓-deref {v = v} {ℓ = low} {high} M⇓a eq)
  rewrite erase-stamp-high v | stamp-val-low v | ⇓-pres-sec sec M⇓a _ _ v eq =
    ⇓ₑ-deref-● (sim sec M⇓a)
sim sec (⇓-deref {v = v} {ℓ = high} {low} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim sec M⇓a)
sim sec (⇓-deref {v = v} {ℓ = high} {high} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim sec M⇓a)
sim {pc = pc} sec (⇓-assign? {L = L} {M} {V} {ℓ = ℓ} {ℓ₁} L⇓a M⇓V pc⋎ℓ≼ℓ₁)
  with ℓ | ℓ₁
...   | low | low =
  ⇓ₑ-assign? (sim sec L⇓a) goal pc⋎ℓ≼ℓ₁
  where
  goal : erase-μᴸ _ ∣ _ ⊢ erase M ⇓ₑ
      erase (stamp-val V (⇓-value M⇓V) low) ∣ erase-μᴸ _
  goal rewrite stamp-val-low (⇓-value M⇓V) = sim (⇓-pres-sec sec L⇓a) M⇓V
...   | low | high =
  ⇓ₑ-assign?-● (sim sec L⇓a) (sim (⇓-pres-sec sec L⇓a) M⇓V)
...   | high | high =
  ⇓ₑ-assign?-● (sim sec L⇓a) (sim (⇓-pres-sec sec L⇓a) M⇓V)
...   | high | low with pc
...   | low  = case pc⋎ℓ≼ℓ₁ of λ where ()
...   | high = case pc⋎ℓ≼ℓ₁ of λ where ()
