module Simulator.CheckerErrAgn where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List hiding ([_])
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Common.Utils
open import Common.Types
open import Memory.Addr
open import Simulator.AST


{- Each case of the `check` function below reflects
   its corresponding rule in `Precision` -}
check-⊑? : (t₁ t₂ : AST) → 𝔹
-- first get rid of all the `cast-pc`s
check-⊑? (castpc _ t _) t′ = check-⊑? t t′
check-⊑? t (castpc _ t′ _) = check-⊑? t t′
-- in most cases we expect the two sides to be syntactically equal
-- Var
check-⊑? (var x _) (var y _) = isYes (x ≟ y)
-- Const
check-⊑? (const {ι} k ℓ _) (const {ι′} k′ ℓ′ _) =
  case ` ι ≡ᵣ? ` ι′ of λ where
  (yes refl) → (isYes (const-eq? k k′)) ∧ (isYes (ℓ =? ℓ′))
  (no  _)    → false
-- Addr
check-⊑? (addr a ℓ _) (addr a′ ℓ′ _) =
  (isYes (addr-eq? a a′)) ∧ (isYes (ℓ =? ℓ′))
-- Lam
check-⊑? (lam ℓᶜ A t ℓ _) (lam ℓᶜ′ A′ t′ ℓ′ _) =
  (isYes (ℓᶜ =? ℓᶜ′)) ∧ (isYes (ℓ =? ℓ′)) ∧
  (isYes (A ⊑? A′))   ∧ (check-⊑? t t′)
-- App
check-⊑? (app t₁ t₂ _) (app t₁′ t₂′ _) = (check-⊑? t₁ t₁′) ∧ (check-⊑? t₂ t₂′)
-- If
check-⊑? (cond t₁ t₂ t₃ _) (cond t₁′ t₂′ t₃′ _) =
  (check-⊑? t₁ t₁′) ∧ (check-⊑? t₂ t₂′) ∧ (check-⊑? t₃ t₃′)
-- Let
check-⊑? (let-bind t₁ t₂ _) (let-bind t₁′ t₂′ _) =
  (check-⊑? t₁ t₁′) ∧ (check-⊑? t₂ t₂′)
-- Ref, Ref?, and Ref✓
check-⊑? (ref ℓ t _) (ref ℓ′ t′ _) = isYes (ℓ =? ℓ′) ∧ (check-⊑? t t′)
check-⊑? (ref? ℓ t _) (ref? ℓ′ t′ _) = isYes (ℓ =? ℓ′) ∧ (check-⊑? t t′)
check-⊑? (ref✓ ℓ t _) (ref✓ ℓ′ t′ _) = isYes (ℓ =? ℓ′) ∧ (check-⊑? t t′)
-- -- Deref
check-⊑? (deref t _) (deref t′ _) = check-⊑? t t′
-- Assign, Assign?, and Assign✓
check-⊑? (assign t₁ t₂ _) (assign t₁′ t₂′ _) = check-⊑? t₁ t₁′ ∧ check-⊑? t₂ t₂′
check-⊑? (assign? t₁ t₂ _) (assign? t₁′ t₂′ _) = check-⊑? t₁ t₁′ ∧ check-⊑? t₂ t₂′
check-⊑? (assign? t₁ t₂ _) (assign  t₁′ t₂′ _) = check-⊑? t₁ t₁′ ∧ check-⊑? t₂ t₂′
check-⊑? (assign✓ t₁ t₂ _) (assign✓ t₁′ t₂′ _) = check-⊑? t₁ t₁′ ∧ check-⊑? t₂ t₂′
check-⊑? (assign✓ t₁ t₂ _) (assign  t₁′ t₂′ _) = check-⊑? t₁ t₁′ ∧ check-⊑? t₂ t₂′
-- Prot
check-⊑? (protect ℓ t _) (protect ℓ′ t′ _) =
  isYes (ℓ =? ℓ′) ∧ check-⊑? t t′
-- Cast
check-⊑? (cast t A B) (cast t′ A′ B′) =
  (isYes (A ⊑? A′) ∧ isYes (B ⊑? B′) ∧ check-⊑? t t′) ∨
  (isYes (A ⊑? B′) ∧ isYes (B ⊑? B′) ∧ check-⊑? t (cast t′ A′ B′)) ∨
  (isYes (B ⊑? A′) ∧ isYes (B ⊑? B′) ∧ check-⊑? (cast t A B) t′)
-- Special case: cast on the left, error on the right
check-⊑? (cast t A B) (err e A′) =
  {- relate by castₗ -}
  (isYes (A ⊑? A′) ∧ isYes (B ⊑? A′) ∧ check-⊑? t (err e A′)) ∨
  {- relate by err   -}
  (isYes (B ⊑? A′))
-- CastL
check-⊑? (cast t A B) t′ =
  let A′ = get-type t′ in
  isYes (A ⊑? A′) ∧ isYes (B ⊑? A′) ∧ check-⊑? t t′
-- CastR
check-⊑? t (cast t′ A′ B′) =
  let A = get-type t in
  isYes (A ⊑? A′) ∧ isYes (A ⊑? B′) ∧ check-⊑? t t′
-- Err
check-⊑? t (err e A′) =
  let A = get-type t in
  isYes (A ⊑? A′)
-- Otherwise
check-⊑? _ _ = false
