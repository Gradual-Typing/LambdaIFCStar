module Utils where

open import Data.List
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.Nat
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Function using (case_of_)


nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ ls) zero    = just x
nth (x ∷ ls) (suc k) = nth ls k


{- Works on association list List (K × V);
   similar to `assoc` in Scheme but has a different
   name because we use "assoc" for associativity.
-}
find : ∀ {K V : Set} → (∀ (k₁ k₂ : K) → Dec (k₁ ≡ k₂)) → List (K × V) → K → Maybe V
find _≟_ [] _ = nothing
find _≟_ (⟨ k₀ , v₀ ⟩ ∷ l) k =
  case k ≟ k₀ of λ where
    (yes _) → just v₀
    (no  _) → find _≟_ l k


snoc-here : ∀ {X} (x : X) → ∀ xs → nth (xs ∷ʳ x) (length xs) ≡ just x
snoc-here x [] = refl
snoc-here x (_ ∷ xs) = snoc-here x xs

snoc-there : ∀ {X} (x : X) → ∀ xs {n y} → nth (xs ∷ʳ y) n ≡ just x → n ≢ length xs → nth xs n ≡ just x
snoc-there x [] {zero} refl neq = contradiction refl neq
snoc-there x (y ∷ xs) {zero} eq neq = eq
snoc-there x (y ∷ xs) {suc n} eq neq = snoc-there x xs eq n≢len
  where
  n≢len : n ≢ length xs
  n≢len n≡len = contradiction (cong suc n≡len) neq


-- infix 4 _⊇_

-- _⊇_ : ∀ {X : Set} (xs ys : List X) → Set
-- xs ⊇ ys = ∀ n {x} → nth ys n ≡ just x → nth xs n ≡ just x

-- {- Properties about _⊇_ : -}
-- ⊇-refl : ∀ {X : Set} (xs : List X) → xs ⊇ xs
-- ⊇-refl xs n eq = eq

-- ⊇-snoc : ∀ {X : Set} (xs : List X) → ∀ x → xs ∷ʳ x ⊇ xs
-- ⊇-snoc (_ ∷ xs) x zero eq = eq
-- ⊇-snoc (_ ∷ xs) x (suc n) eq = ⊇-snoc xs x n eq


pattern ⟨_,_,_⟩ x y z = ⟨ x , ⟨ y , z ⟩ ⟩
pattern ⟨_,_,_,_⟩ x y z w = ⟨ x , ⟨ y , ⟨ z , w ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_⟩ x y z w u = ⟨ x , ⟨ y , ⟨ z , ⟨ w , u ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_⟩ x y z w u v = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , v ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_⟩ x y z w u v p = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , p ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_⟩ x y z w u v p q = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , q ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , i ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i j = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , ⟨ i , j ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

pattern ∅ = ⟨ [] , [] ⟩
