module CanonicalErased where

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
open import Heap
open import CC
open import WellTyped

open import Erasure

data ErasedFun : Term → Set where

  ϵ-fun-● : ErasedFun ●

  ϵ-fun-ƛ : ∀ {pc A N} → ErasedFun (ƛ[ pc ] A ˙ N of low)

canonical-fun-erase : ∀ {Σ gc gc′ pc A B g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ [ gc′ ] A ⇒ B of g
  → Value V
  → ∃[ V′ ] V′ ≡ erase V × ErasedFun V′
canonical-fun-erase {gc = gc} {pc = pc} ⊢V v =
  case canonical-fun ⊢V v of λ where
  (Fun-ƛ {ℓ = low}  _ _) → ⟨ _ , refl , ϵ-fun-ƛ ⟩
  (Fun-ƛ {ℓ = high} _ _) → ⟨ _ , refl , ϵ-fun-● ⟩
  (Fun-proxy fun i sub) →
    case v of λ where
    (V-cast w _) →
      canonical-fun-erase {gc = gc} {pc = pc} (fun-wt fun) w

data ErasedRef : Term → Set where

  ϵ-ref-● : ErasedRef ●

  ϵ-ref-addr : ∀ {n} → ErasedRef (addr a[ low ] n of low)

canonical-ref-erase : ∀ {Σ gc pc A g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
  → Value V
  → ∃[ V′ ] V′ ≡ erase V × ErasedRef V′
canonical-ref-erase {gc = gc} {pc} ⊢V v =
  case canonical-ref ⊢V v of λ where
  (Ref-addr {ℓ = low}  {low}  _ _) → ⟨ _ , refl , ϵ-ref-addr ⟩
  (Ref-addr {ℓ = low}  {high} _ _) → ⟨ _ , refl , ϵ-ref-● ⟩
  (Ref-addr {ℓ = high} {low}  _ _) → ⟨ _ , refl , ϵ-ref-● ⟩
  (Ref-addr {ℓ = high} {high} _ _) → ⟨ _ , refl , ϵ-ref-● ⟩
  (Ref-proxy ref i sub) →
    case v of λ where
    (V-cast w _) →
      canonical-ref-erase {gc = gc} {pc} (ref-wt ref) w
