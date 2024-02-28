module Dyn.BigStep where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils
open import Common.SecurityLabels
open import Dyn.Syntax
open import Dyn.Values
open import Memory.Heap Term Value


infix 2 _∣_⊢_⇓_∣_
data _∣_⊢_⇓_∣_ : Heap → StaticLabel → (M V : Term) → Heap → Set

⇓-value : ∀ {μ μ′ pc M V} → μ ∣ pc ⊢ M ⇓ V ∣ μ′ → Value V

{- only consider evaluation to values -}
data _∣_⊢_⇓_∣_ where

  ⇓-val : ∀ {μ pc V}
    → Value V
      --------------------------- Value
    → μ ∣ pc ⊢ V ⇓ V ∣ μ

  ⇓-app : ∀ {μ μ₁ μ₂ μ₃ pc L M N V W ℓ}
    → μ  ∣ pc     ⊢ L       ⇓ ƛ N of ℓ ∣ μ₁
    → μ₁ ∣ pc     ⊢ M       ⇓ V ∣ μ₂
    → (⇓W : μ₂ ∣ pc ⋎ ℓ ⊢ N [ V ] ⇓ W ∣ μ₃)
      ---------------------------------------------------------------------- Application
    → μ  ∣ pc     ⊢ L · M   ⇓ stamp-val W (⇓-value ⇓W) ℓ ∣ μ₃

  ⇓-if-true : ∀ {μ μ₁ μ₂ pc L M N V ℓ}
    → μ  ∣ pc     ⊢ L ⇓ $ true of ℓ ∣ μ₁
    → (⇓V : μ₁ ∣ pc ⋎ ℓ ⊢ M ⇓ V ∣ μ₂)
      ---------------------------------------------------------------------- IfTrue
    → μ  ∣ pc     ⊢ if L M N ⇓ stamp-val V (⇓-value ⇓V) ℓ ∣ μ₂

  ⇓-if-false : ∀ {μ μ₁ μ₂ pc L M N V ℓ}
    → μ  ∣ pc     ⊢ L ⇓ $ false of ℓ ∣ μ₁
    → (⇓V : μ₁ ∣ pc ⋎ ℓ ⊢ N ⇓ V ∣ μ₂)
      ---------------------------------------------------------------------- IfFalse
    → μ  ∣ pc     ⊢ if L M N ⇓ stamp-val V (⇓-value ⇓V) ℓ ∣ μ₂

  ⇓-ref? : ∀ {μ μ₁ pc M V n ℓ}
    → (⇓V : μ ∣ pc ⊢ M ⇓ V ∣ μ₁)
    → a⟦ ℓ ⟧ n FreshIn μ₁
    → pc ≼ ℓ
      -------------------------------------------------------------------------------------- RefNSU
    → let v = ⇓-value ⇓V in
       μ ∣ pc ⊢ ref?⟦ ℓ ⟧ M ⇓ addr a⟦ ℓ ⟧ n of low ∣
                               cons-μ (a⟦ ℓ ⟧ n) (stamp-val V v ℓ) (stamp-val-value v) μ₁

  ⇓-deref : ∀ {μ μ₁ pc M V v n ℓ ℓ̂}
    → μ ∣ pc ⊢ M ⇓ addr a⟦ ℓ̂ ⟧ n of ℓ ∣ μ₁
    → lookup-μ μ₁ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      ---------------------------------------------------------------------------- Deref
    → μ ∣ pc ⊢ ! M ⇓ stamp-val V v ℓ ∣ μ₁

  ⇓-assign? : ∀ {μ μ₁ μ₂ pc L M V n ℓ ℓ̂}
    → μ  ∣ pc ⊢ L ⇓ addr a⟦ ℓ̂ ⟧ n of ℓ ∣ μ₁
    → (⇓V : μ₁ ∣ pc ⊢ M ⇓ V ∣ μ₂)
    → pc ⋎ ℓ ≼ ℓ̂
      -------------------------------------------------------------------------- AssignNSU
    → let v = ⇓-value ⇓V in
       μ ∣ pc ⊢ L :=? M ⇓ $ tt of low ∣
                           cons-μ (a⟦ ℓ̂ ⟧ n) (stamp-val V v ℓ̂) (stamp-val-value v) μ₂



{- If M ⇓ V then V is Value -}
⇓-value (⇓-val v) = v
⇓-value (⇓-app _ _ ⇓W) = stamp-val-value (⇓-value ⇓W)
⇓-value (⇓-if-true  _ ⇓V) = stamp-val-value (⇓-value ⇓V)
⇓-value (⇓-if-false _ ⇓V) = stamp-val-value (⇓-value ⇓V)
⇓-value (⇓-ref? _ _ _) = V-addr
⇓-value (⇓-deref {v = v} _ _) = stamp-val-value v
⇓-value (⇓-assign? _ _ _) = V-const
