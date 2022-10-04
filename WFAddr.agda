module WFAddr where

open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Utils
open import Types
open import Heap

{- An address is well-formed if it is within the length of the half-heap. -}
data WFAddr_In_ : Addr → Heap → Set where
  wfᴸ : ∀ {n μᴸ μᴴ}
    → n < length μᴸ
    → WFAddr a[ low ] n In ⟨ μᴸ , μᴴ ⟩

  wfᴴ : ∀ {n μᴸ μᴴ}
    → n < length μᴴ
    → WFAddr a[ high ] n In ⟨ μᴸ , μᴴ ⟩

{- Relax by extending the heap -}
wf-relaxᴸ : ∀ {n m μᴸ μᴴ} V v
  → WFAddr (a[ low ] n) In ⟨                 μᴸ , μᴴ ⟩
  → WFAddr (a[ low ] n) In ⟨ ⟨ m , V & v ⟩ ∷ μᴸ , μᴴ ⟩
wf-relaxᴸ {μᴸ = μᴸ} V v (wfᴸ n<len) = wfᴸ (<-trans n<len (n<1+n (length μᴸ)))

wf-relaxᴴ : ∀ {n m μᴸ μᴴ} V v
  → WFAddr (a[ high ] n) In ⟨ μᴸ ,                 μᴴ ⟩
  → WFAddr (a[ high ] n) In ⟨ μᴸ , ⟨ m , V & v ⟩ ∷ μᴴ ⟩
wf-relaxᴴ {μᴴ = μᴴ} V v (wfᴴ n<len) = wfᴴ (<-trans n<len (n<1+n (length μᴴ)))
