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
  cast : AST → Type → Type → AST
  castpc : Label → AST → Type → AST
  err : Type → AST
  -- sub : AST → Type → Type → AST

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
get-type (cast _ _ A) = A
get-type (castpc _ _ A) = A
get-type (err A) = A
-- get-type (sub _ _ A) = A

{- Translates a typing derivation into an AST -}
to-ast : ∀ {Γ Σ gc pc A} M → Γ ; Σ ; gc ; pc ⊢ M ⦂ A → AST
to-ast {A = A} (` x) (⊢var _) = var x A
to-ast {A = A} ($ k of ℓ) ⊢const = const k ℓ A
to-ast {A = A} (addr_of_ a ℓ) (⊢addr _) = addr a ℓ A
to-ast {A = B} (ƛ⟦ pc ⟧ A ˙ N of ℓ) (⊢lam ⊢N) =
  lam pc A (to-ast {pc = low} N ⊢N) ℓ B
to-ast {A = A} (L · M) (⊢app ⊢L ⊢M) = app (to-ast L ⊢L) (to-ast M ⊢M) A
to-ast {A = A} (if L _ M N) (⊢if ⊢L ⊢M ⊢N) =
  cond (to-ast L ⊢L) (to-ast {pc = low} M ⊢M) (to-ast {pc = low} N ⊢N) A
to-ast {A = A} (`let M N) (⊢let ⊢M ⊢N) =
  let-bind (to-ast M ⊢M) (to-ast {pc = low} N ⊢N) A
to-ast {A = A} (ref⟦ ℓ ⟧ M) (⊢ref ⊢M _) = ref ℓ (to-ast M ⊢M) A
to-ast {A = A} (ref?⟦ ℓ ⟧ M) (⊢ref? ⊢M) = ref? ℓ (to-ast M ⊢M) A
to-ast {A = A} (ref✓⟦ ℓ ⟧ M) (⊢ref✓ ⊢M _) = ref✓ ℓ (to-ast M ⊢M) A
to-ast {A = A} (! M) (⊢deref ⊢M) = deref (to-ast M ⊢M) A
to-ast {A = A} (L := M) (⊢assign ⊢L ⊢M _) = assign (to-ast L ⊢L) (to-ast M ⊢M) A
to-ast {A = A} (L :=? M) (⊢assign? ⊢L ⊢M) =
  assign? (to-ast L ⊢L) (to-ast {pc = low} M ⊢M) A
to-ast {A = A} (L :=✓ M) (⊢assign✓ ⊢L ⊢M _) =
  assign✓ (to-ast L ⊢L) (to-ast M ⊢M) A
to-ast {A = A} (prot ℓ M) (⊢prot ⊢M) = protect ℓ (to-ast M ⊢M) A
to-ast {A = B} (M ⟨ c ⟩) (⊢cast {A = A} {.B} ⊢M) = cast (to-ast M ⊢M) A B
to-ast {A = A} (cast-pc g M) (⊢cast-pc ⊢M _) = castpc g (to-ast M ⊢M) A
to-ast {A = A} (error e) ⊢err = err A
to-ast {A = B} M (⊢sub ⊢M _) = to-ast M ⊢M
-- to-ast {A = B} M (⊢sub {A = A} {.B} ⊢M _) = sub (to-ast M ⊢M) A B
to-ast M (⊢sub-pc ⊢M _) = to-ast M ⊢M

M : Term
M = (ƛ⟦ low ⟧ ` Bool of l high ˙ ` 0 of low) · ($ true of low)

⊢M : [] ; ∅ ; l low ; low ⊢ M ⦂ ` Bool of l high
⊢M = ⊢app (⊢lam (⊢var refl)) (⊢sub ⊢const (<:-ty (<:-l l≼h) <:-ι))

t = to-ast M ⊢M
