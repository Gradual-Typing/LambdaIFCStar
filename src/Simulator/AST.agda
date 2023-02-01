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
to-ast : ∀ {Γ Σ gc pc A} M → Γ ; Σ ; gc ; pc ⊢ M ⦂ A → (A′ : Type) → (A <: A′) → AST
to-ast (` x) (⊢var _) A′ _ = var x A′
to-ast ($ k of ℓ) ⊢const A′ _ = const k ℓ A′
to-ast (addr_of_ a ℓ) (⊢addr _) A′ _ = addr a ℓ A′
to-ast (ƛ⟦ pc ⟧ A ˙ N of ℓ) (⊢lam ⊢N) A′ _ =
  lam pc A (to-ast {pc = low} N ⊢N _ <:-refl) ℓ A′
to-ast (L · M) (⊢app ⊢L ⊢M) A′ _ =
  app (to-ast L ⊢L _ <:-refl) (to-ast M ⊢M _ <:-refl) A′
to-ast (if L _ M N) (⊢if ⊢L ⊢M ⊢N) A′ _ =
  cond (to-ast            L ⊢L _ <:-refl)
       (to-ast {pc = low} M ⊢M _ <:-refl)
       (to-ast {pc = low} N ⊢N _ <:-refl) A′
to-ast (`let M N) (⊢let ⊢M ⊢N) A′ _ =
  let-bind (to-ast M ⊢M _ <:-refl) (to-ast {pc = low} N ⊢N _ <:-refl) A′
to-ast (ref⟦ ℓ ⟧ M) (⊢ref ⊢M _) A′ _ =
  ref  ℓ (to-ast M ⊢M _ <:-refl) A′
to-ast (ref?⟦ ℓ ⟧ M) (⊢ref? ⊢M) A′ _ =
  ref? ℓ (to-ast M ⊢M _ <:-refl) A′
to-ast (ref✓⟦ ℓ ⟧ M) (⊢ref✓ ⊢M _) A′ _ =
  ref✓ ℓ (to-ast M ⊢M _ <:-refl) A′
to-ast (! M) (⊢deref ⊢M) A′ _ =
  deref (to-ast M ⊢M _ <:-refl) A′
to-ast (L := M) (⊢assign ⊢L ⊢M _) A′ _ =
  assign (to-ast L ⊢L _ <:-refl) (to-ast M ⊢M _ <:-refl) A′
to-ast (L :=? M) (⊢assign? ⊢L ⊢M) A′ _ =
  assign? (to-ast L ⊢L _ <:-refl) (to-ast {pc = low} M ⊢M _ <:-refl) A′
to-ast (L :=✓ M) (⊢assign✓ ⊢L ⊢M _) A′ _ =
  assign✓ (to-ast L ⊢L _ <:-refl) (to-ast M ⊢M _ <:-refl) A′
to-ast (prot ℓ M) (⊢prot ⊢M) A′ _ =
  protect ℓ (to-ast M ⊢M _ <:-refl) A′
to-ast {A = B} (M ⟨ c ⟩) (⊢cast {A = A} {.B} ⊢M) A′ _ =
  cast (to-ast M ⊢M _ <:-refl) A B A′
to-ast (cast-pc g M) (⊢cast-pc ⊢M _) A′ _ =
  castpc g (to-ast M ⊢M _ <:-refl) A′
to-ast (error e) ⊢err A′ _ = err e A′
to-ast {A = B} M (⊢sub {A = A} {.B} ⊢M A<:B) A′ B<:A′ =
  to-ast M ⊢M A′ (<:-trans A<:B B<:A′)
to-ast M (⊢sub-pc ⊢M _) A′ A<:A′ =
  to-ast M ⊢M A′ A<:A′
