open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC


module Reduction where

open import Frame public

infix 2 _∣_∣_—→_∣_

data _∣_∣_—→_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ pc}
    → M        ∣ μ ∣ pc —→ M′        ∣ μ′
      ---------------------------------------------- ξ
    → plug M F ∣ μ ∣ pc —→ plug M′ F ∣ μ′

  ξ-err : ∀ {F μ pc e}
      ---------------------------------------------- ξ-error
    → plug (error e) F ∣ μ ∣ pc —→ error e ∣ μ

  prot-val : ∀ {V μ pc ℓ}
    → (v : Value V)
      --------------------------------------------------- ProtectVal
    → prot ℓ V ∣ μ ∣ pc —→ stamp-val V v ℓ ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ pc ℓ}
    → M        ∣ μ ∣ pc ⋎ ℓ —→ M′        ∣ μ′
      --------------------------------------------------- ProtectContext
    → prot ℓ M ∣ μ ∣ pc     —→ prot ℓ M′ ∣ μ′

  prot-err : ∀ {μ pc ℓ e}
      --------------------------------------------------- ProtectContext
    → prot ℓ (error e) ∣ μ ∣ pc —→ error e ∣ μ

  β : ∀ {V N μ pc pc′ A ℓ}
    → Value V
      ------------------------------------------------------------------- β
    → (ƛ[ pc′ ] A ˙ N of ℓ) · V ∣ μ ∣ pc —→ prot ℓ (N [ V ]) ∣ μ

  β-if-true : ∀ {M N μ pc A ℓ}
      ----------------------------------------------------------------------- IfTrue
    → if ($ true of ℓ) A M N ∣ μ ∣ pc —→ prot ℓ M ∣ μ

  β-if-false : ∀ {M N μ pc A ℓ}
      ----------------------------------------------------------------------- IfFalse
    → if ($ false of ℓ) A M N ∣ μ ∣ pc —→ prot ℓ N ∣ μ

  β-let : ∀ {V N μ pc}
    → Value V
      -------------------------------------- Let
    → `let V N ∣ μ ∣ pc —→ N [ V ] ∣ μ

  ref-static : ∀ {M μ pc ℓ}
      ------------------------------------------------- RefStatic
    → ref[ ℓ ] M ∣ μ ∣ pc —→ ref✓[ ℓ ] M ∣ μ

  ref?-ok : ∀ {M μ pc ℓ}
    → pc ≼ ℓ
      ------------------------------------------------- RefNSUSuccess
    → ref?[ ℓ ] M ∣ μ ∣ pc —→ ref✓[ ℓ ] M ∣ μ

  ref?-fail : ∀ {M μ pc ℓ}
    → ¬ pc ≼ ℓ
      ------------------------------------------------- RefNSUFail
    → ref?[ ℓ ] M ∣ μ ∣ pc —→ error nsu-error ∣ μ

  ref : ∀ {V μ pc n ℓ}
    → (v : Value V)
    → a[ ℓ ] n FreshIn μ  {- address is fresh -}
      -------------------------------------------------------------------------------- Ref
    → ref✓[ ℓ ] V ∣ μ ∣ pc —→ addr (a[ ℓ ] n) of low ∣ cons-μ (a[ ℓ ] n) V v μ

  deref : ∀ {V μ pc v n ℓ ℓ₁}
    → lookup-μ μ (a[ ℓ₁ ] n) ≡ just (V & v)
      --------------------------------------------------------------------- Deref
    → ! (addr (a[ ℓ₁ ] n) of ℓ) ∣ μ ∣ pc —→ prot (ℓ₁ ⋎ ℓ) V ∣ μ

  assign-static : ∀ {L M μ pc}
      ------------------------------------------------------- AssignStatic
    → L := M ∣ μ ∣ pc —→ L :=✓ M ∣ μ

  assign?-ok : ∀ {M μ pc n ℓ ℓ₁}
    → pc ≼ ℓ₁
      ----------------------------------------------------------------------------- AssignNSUSuccess
    → (addr (a[ ℓ₁ ] n) of ℓ) :=? M ∣ μ ∣ pc —→ (addr (a[ ℓ₁ ] n) of ℓ) :=✓ M ∣ μ

  assign?-fail : ∀ {M μ pc n ℓ ℓ₁}
    → ¬ pc ≼ ℓ₁
      ----------------------------------------------------------------------------- AssignNSUFail
    → (addr (a[ ℓ₁ ] n) of ℓ) :=? M ∣ μ ∣ pc —→ error nsu-error ∣ μ

  assign : ∀ {V μ pc n ℓ ℓ₁}
    → (v : Value V)
      ---------------------------------------------------------------------------------------------- Assign
    → (addr (a[ ℓ₁ ] n) of ℓ) :=✓ V ∣ μ ∣ pc —→ $ tt of low ∣ cons-μ (a[ ℓ₁ ] n) V v μ

  {- Reduction rules about casts, active and inert: -}
  cast : ∀ {A B V M μ pc} {c : Cast A ⇒ B}
    → Value V → Active c
    → ApplyCast V , c ↝ M
      -------------------------------------------------- Cast
    → V ⟨ c ⟩ ∣ μ ∣ pc —→ M ∣ μ

  if-cast-true : ∀ {M N μ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastTrue
    → if ($ true of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ prot ℓ (cast-pc ⋆ M) ⟨ branch/c A ℓ c ⟩ ∣ μ

  if-cast-false : ∀ {M N μ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastFalse
    → if ($ false of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ prot ℓ (cast-pc ⋆ N) ⟨ branch/c A ℓ c ⟩ ∣ μ

  fun-cast : ∀ {V W μ pc A B C D gc₁ gc₂ g₁ g₂} {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
    → Value V → Value W
    → (i : Inert c)
      ---------------------------------------------------------------- FunCast
    → (V ⟨ c ⟩) · W ∣ μ ∣ pc —→ elim-fun-proxy V W i pc ∣ μ

  deref-cast : ∀ {V μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → Inert c
      ------------------------------------------------------ DerefCast
    → ! (V ⟨ c ⟩) ∣ μ ∣ pc —→ ! V ⟨ out/c c ⟩ ∣ μ

  assign?-cast : ∀ {V M μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → (i : Inert c)
      ----------------------------------------------------------------------------- AssignNSUCast
    → (V ⟨ c ⟩) :=? M ∣ μ ∣ pc —→ elim-ref-proxy V M i _:=?_ ∣ μ

  assign-cast : ∀ {V W μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V → Value W
    → (i : Inert c)
      --------------------------------------------------------------------------------------------- AssignCast
    → (V ⟨ c ⟩) :=✓ W ∣ μ ∣ pc —→ elim-ref-proxy V W i _:=✓_ {- V := (W ⟨ in/c c ⟩) -} ∣ μ

  β-cast-pc : ∀ {V μ pc g}
    → Value V
      ------------------------------------- CastPC
    → cast-pc g V ∣ μ ∣ pc —→ V ∣ μ


{- Multi-step reduction -}
infix  2 _∣_∣_—↠_∣_
infixr 2 _∣_∣_—→⟨_⟩_
infix  3 _∣_∣_∎

data _∣_∣_—↠_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

    _∣_∣_∎ : ∀ M μ pc
        -----------------------------------
      → M ∣ μ ∣ pc —↠ M ∣ μ

    _∣_∣_—→⟨_⟩_ : ∀ L μ pc {M N μ′ μ″}
      → L ∣ μ  ∣ pc —→ M ∣ μ′
      → M ∣ μ′ ∣ pc —↠ N ∣ μ″
        -----------------------------------
      → L ∣ μ  ∣ pc —↠ N ∣ μ″
