module Heap where

open import Data.Nat using (ℕ; _≟_)
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Types
open import HeapContext public
open import CC using (Term; Value)

{- n ↦ V
  We use an association list that is split into low- and high- halves to represent the heap.
-}
data Cell : Set where
  _&_ : (V : Term) → .(Value V) → Cell

HalfHeap = List (RawAddr × Cell)
Heap     = HalfHeap {- low -} × HalfHeap {- high -}

lookup-μ : Heap → Addr → Maybe Cell
lookup-μ ⟨ μᴸ , μᴴ ⟩ (a[ low  ] n) = find _≟_ μᴸ n
lookup-μ ⟨ μᴸ , μᴴ ⟩ (a[ high ] n) = find _≟_ μᴴ n

cons-μ : Addr → (V : Term) → Value V → Heap → Heap
cons-μ (a[ low  ] n) V v ⟨ μᴸ , μᴴ ⟩ = ⟨ ⟨ n , V & v ⟩ ∷ μᴸ , μᴴ ⟩
cons-μ (a[ high ] n) V v ⟨ μᴸ , μᴴ ⟩ = ⟨ μᴸ , ⟨ n , V & v ⟩ ∷ μᴴ ⟩

infix 10 _FreshIn_

_FreshIn_ : Addr → Heap → Set
a[ low  ] n FreshIn ⟨ μᴸ , μᴴ ⟩ = n ≡ length μᴸ
a[ high ] n FreshIn ⟨ μᴸ , μᴴ ⟩ = n ≡ length μᴴ

{- Generate a fresh address for heap μ -}
gen-fresh : ∀ μ {ℓ} → ∃[ n ] (a[ ℓ ] n FreshIn μ)
gen-fresh ⟨ μᴸ , μᴴ ⟩ {low } = ⟨ length μᴸ , refl ⟩
gen-fresh ⟨ μᴸ , μᴴ ⟩ {high} = ⟨ length μᴴ , refl ⟩
