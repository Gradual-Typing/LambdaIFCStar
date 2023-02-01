module Simulator.AST where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Memory.Addr
open import CC.CCStatics


{- Each AST node embeds its type -}
data AST : Set where
  var : (n : ℕ) → Type → AST
  const : ∀ {ι} → (k : rep ι) → StaticLabel → Type → AST
  addr : Addr → StaticLabel → Type → AST
  lam : StaticLabel → Type → AST → StaticLabel → Type → AST
  app : AST → AST → Type → AST
  cond : AST → AST → AST → Type → AST
  let-bind : AST → AST → Type → AST
  ref : StaticLabel → AST → Type → AST
  ref? : StaticLabel → AST → Type → AST
  ref✓ : StaticLabel → AST → Type → AST
  deref : AST → Type → AST
  assign : AST → AST → Type → AST
  assign? : AST → AST → Type → AST
  assign✓ : AST → AST → Type → AST
  protect : StaticLabel → AST → Type → AST
  cast : AST → Type → Type → Type → AST
  castpc : Label → AST → Type → AST
  err : Error → Type → AST


get-type : AST → Type
get-type (var _ A) = A
get-type (const _ _ A) = A
get-type (addr _ _ A) = A
get-type (lam _ _ _ _ A) = A
get-type (app _ _ A) = A
get-type (cond _ _ _ A) = A
get-type (let-bind _ _ A) = A
get-type (ref _ _ A) = A
get-type (ref? _ _ A) = A
get-type (ref✓ _ _ A) = A
get-type (deref _ A) = A
get-type (assign _ _ A) = A
get-type (assign? _ _ A) = A
get-type (assign✓ _ _ A) = A
get-type (protect _ _ A) = A
get-type (cast _ A B A′) = A′
get-type (castpc _ _ A) = A
get-type (err e A) = A

{- Translates a typing derivation into an AST -}
to-ast : ∀ {Γ Σ gc pc A} M → Γ ; Σ ; gc ; pc ⊢ M ⦂ A → (A′ : Type) → AST
to-ast (` x) (⊢var _) A′ = var x A′
to-ast ($ k of ℓ) ⊢const A′ = const k ℓ A′
to-ast (addr_of_ a ℓ) (⊢addr _) A′ = addr a ℓ A′
to-ast (ƛ⟦ pc ⟧ A ˙ N of ℓ) (⊢lam {B = B} ⊢N) A′ =
  lam pc A (to-ast {pc = low} N ⊢N B) ℓ A′
to-ast (L · M) (⊢app {gc = gc} {A = A} {B} {g = g} ⊢L ⊢M) A′ =
  app (to-ast L ⊢L (⟦ gc ⋎̃ g ⟧ A ⇒ B of g)) (to-ast M ⊢M A) A′
to-ast (if L A M N) (⊢if {g = g} ⊢L ⊢M ⊢N) A′ =
  cond (to-ast L ⊢L (` Bool of g))
       (to-ast {pc = low} M ⊢M A)
       (to-ast {pc = low} N ⊢N A) A′
to-ast (`let M N) (⊢let {A = A} {B} ⊢M ⊢N) A′ =
  let-bind (to-ast M ⊢M A) (to-ast {pc = low} N ⊢N B) A′
to-ast (ref⟦ ℓ ⟧ M) (⊢ref {T = T} {ℓ} ⊢M _) A′ =
  ref  ℓ (to-ast M ⊢M (T of l ℓ)) A′
to-ast (ref?⟦ ℓ ⟧ M) (⊢ref? {T = T} {ℓ} ⊢M) A′ =
  ref? ℓ (to-ast M ⊢M (T of l ℓ)) A′
to-ast (ref✓⟦ ℓ ⟧ M) (⊢ref✓ {T = T} {ℓ} ⊢M _) A′ =
  ref✓ ℓ (to-ast M ⊢M (T of l ℓ)) A′
to-ast (! M) (⊢deref {A = A} {g} ⊢M) A′ =
  deref (to-ast M ⊢M (Ref A of g)) A′
to-ast (L := M) (⊢assign {T = T} {ℓ} ⊢L ⊢M _) A′ =
  assign (to-ast L ⊢L (Ref (T of l ℓ) of l ℓ)) (to-ast M ⊢M (T of l ℓ)) A′
to-ast (L :=? M) (⊢assign? {T = T} {g} ⊢L ⊢M) A′ =
  assign? (to-ast L ⊢L (Ref (T of g) of g)) (to-ast {pc = low} M ⊢M (T of g)) A′
to-ast (L :=✓ M) (⊢assign✓ {T = T} {ℓ} ⊢L ⊢M _) A′ =
  assign✓ (to-ast L ⊢L (Ref (T of l ℓ) of l ℓ)) (to-ast M ⊢M (T of l ℓ)) A′
to-ast (prot ℓ M) (⊢prot {A = A} ⊢M) A′ =
  protect ℓ (to-ast M ⊢M A) A′
to-ast {A = B} (M ⟨ c ⟩) (⊢cast {A = A} {.B} ⊢M) A′ =
  cast (to-ast M ⊢M A) A B A′
to-ast (cast-pc g M) (⊢cast-pc {A = A} ⊢M _) A′ =
  castpc g (to-ast M ⊢M A) A′
to-ast (error e) ⊢err A′ = err e A′
to-ast {A = B} M (⊢sub {A = A} {.B} ⊢M A<:B) A′ =
  to-ast M ⊢M A′
to-ast M (⊢sub-pc ⊢M _) A′ =
  to-ast M ⊢M A′
