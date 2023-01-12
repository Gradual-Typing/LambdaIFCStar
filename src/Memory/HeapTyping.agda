{- Σ ⊢ μ : heap μ is well-typed under context Σ -}

open import Common.Types
open import Memory.HeapContext using (HeapContext)

module Memory.HeapTyping
  (Term : Set)
  (Value : Term → Set)
  (_;_;_;_⊢_⦂_ : Context → HeapContext → Label → StaticLabel → Term → Type → Set)
  where

open import Data.Nat
open import Data.Nat.Properties using (n≮n; <-trans; n<1+n; ≤-refl)
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Memory.HeapContext hiding (Addr; RawAddr; a⟦_⟧_; addr-eq?) public
open import Memory.Heap        Term Value                    public
open import Memory.WFAddr      Term Value                    public


infix 4 _⊢_

_⊢_ : HeapContext → Heap → Set
Σ ⊢ μ = ∀ n ℓ {T}
  → lookup-Σ Σ (a⟦ ℓ ⟧ n) ≡ just T
  → (WFAddr a⟦ ℓ ⟧ n In μ) ×
     (∃[ V ] ∃[ v ] lookup-μ μ (a⟦ ℓ ⟧ n) ≡ just (V & v) × [] ; Σ ; l low ; low ⊢ V ⦂ (T of l ℓ))
