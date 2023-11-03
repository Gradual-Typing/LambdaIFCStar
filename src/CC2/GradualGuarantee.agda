module CC2.GradualGuarantee where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import Memory.HeapContext
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)

open import Simulation.CatchUp using (catchup)
open import Simulation.Simulation using (sim)

dgg-left : ∀ {Σ₁ Σ₁′ A A′ M M′ V′ μ₁ μ₁′ μ₂′}
  → [] ; [] ∣ Σ₁ ; Σ₁′ ∣ l low ; l low ∣ low ; low ⊢ M ⊑ M′ ⇐ A ⊑ A′
  → Σ₁ ⊑ₘ Σ₁′
  → Σ₁ ; Σ₁′ ⊢ μ₁ ⊑ μ₁′
  → SizeEq μ₁ μ₁′
  → M′ ∣ μ₁′ ∣ l low —↠ V′ ∣ μ₂′
  → Value V′
    -----------------------------------------
  → ∃[ V ] ∃[ μ₂ ] ∃[ Σ₂ ] ∃[ Σ₂′ ]
       (M ∣ μ₁ ∣ l low —↠ V ∣ μ₂) ×
       ([] ; [] ∣ Σ₂ ; Σ₂′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ V′ ⇐ A ⊑ A′)
dgg-left {Σ₁} {Σ₁′} {μ₁ = μ} M⊑V′ Σ₁⊑Σ₁′ μ₁⊑μ₁′ size-eq (_ ∣ _ ∣ .(l low) ∎) v′ =
  case catchup {μ = μ} {PC = l low} v′ M⊑V′ of λ where
  ⟨ V , v , M↠V , V⊑V′ ⟩ → ⟨ V , μ , Σ₁ , Σ₁′ , M↠V , V⊑V′ ⟩
dgg-left M⊑M′ Σ₁⊑Σ₁′ μ₁⊑μ₁′ size-eq (_ ∣ _ ∣ .(l low) —→⟨ M′→N′ ⟩ N′↠V′) v′ =
  case sim v-l v-l M⊑M′ Σ₁⊑Σ₁′ μ₁⊑μ₁′ ⊑-l size-eq M′→N′ of λ where
  ⟨ Σ₂ , Σ₂′ , _ , _ , Σ₂⊑Σ₂′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ →
    case dgg-left N⊑N′ Σ₂⊑Σ₂′ μ₂⊑μ₂′ size-eq′ N′↠V′ v′ of λ where
    ⟨ V , μ₃ , Σ₃ , Σ₃′ , N↠V , V⊑V′ ⟩ →
      ⟨ V , μ₃ , Σ₃ , Σ₃′ , trans-mult M↠N N↠V , V⊑V′ ⟩
