module CCExpSub.Reduction where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CCExpSub.Statics
open import CCExpSub.CanonicalForms
open import Memory.Heap Term Value

-- open import CC.ApplyCast        public
open import CCExpSub.ProxyElimination public
open import CCExpSub.Frame            public


infix 2 _∣_∣_—→_∣_

data _∣_∣_—→_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

  ξ : ∀ {Σ gcₒ gcᵢ pc A B M M′ μ μ′} {F : Frame Σ gcₒ gcᵢ pc A B}
    → [] ; Σ ; gcᵢ ; pc ⊢ M ⦂ A
    → M        ∣ μ ∣ pc —→ M′        ∣ μ′
      ---------------------------------------------- ξ
    → plug M F ∣ μ ∣ pc —→ plug M′ F ∣ μ′

  ξ-err : ∀ {Σ gcₒ gcᵢ pc A B μ e} {F : Frame Σ gcₒ gcᵢ pc A B}
      ---------------------------------------------- ξ-Error
    → plug (error A e) F ∣ μ ∣ pc —→ error B e ∣ μ

  prot-val : ∀ {V μ pc ℓ}
    → (v : Value V)
      --------------------------------------------------- ProtectVal
    → prot ℓ V ∣ μ ∣ pc —→ stamp-val V v ℓ ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ pc ℓ}
    → M        ∣ μ ∣ pc ⋎ ℓ —→ M′        ∣ μ′
      --------------------------------------------------- ProtectContext
    → prot ℓ M ∣ μ ∣ pc     —→ prot ℓ M′ ∣ μ′

  prot-err : ∀ {μ pc ℓ A e}
      --------------------------------------------------- ProtectErr
    → prot ℓ (error A e) ∣ μ ∣ pc —→ error (stamp A (l ℓ)) e ∣ μ

  β : ∀ {V N μ pc pc′ A ℓ}
    → Value V
      ------------------------------------------------------------------- β
    → (ƛ⟦ pc′ ⟧ A ˙ N of ℓ) · V ∣ μ ∣ pc —→ prot ℓ (N [ V ]) ∣ μ

  β-if-true : ∀ {M N μ pc A ℓ}
      ----------------------------------------------------------------------- IfTrue
    → if ($ true of ℓ) A M N ∣ μ ∣ pc —→ prot ℓ M ∣ μ

  β-if-false : ∀ {M N μ pc A ℓ}
      ----------------------------------------------------------------------- IfFalse
    → if ($ false of ℓ) A M N ∣ μ ∣ pc —→ prot ℓ N ∣ μ

  if-cast : ∀ {V M N μ pc A g} {c : Cast ` Bool of g ⇒ ` Bool of ⋆}
    → Value V
    → Inert c
      --------------------------------------------------------------------------------- IfCast
    → if (V ⟨ c ⟩) A M N ∣ μ ∣ pc —→ (cast-pc ⋆ (if V A M N)) ⟨ branch/c A c ⟩ ∣ μ

  if-sub : ∀ {V M N μ pc A g₁ g₂} {s : ` Bool of g₁ ↟ ` Bool of g₂}
    → SimpleValue V
      --------------------------------------------------------------------------------- IfSub
    → if (V ↟⟨ s ⟩) A M N ∣ μ ∣ pc —→ (if V A M N) ↟⟨ branch/s A s ⟩ ∣ μ

  β-let : ∀ {V N μ pc}
    → Value V
      -------------------------------------- Let
    → `let V N ∣ μ ∣ pc —→ N [ V ] ∣ μ

  ref-static : ∀ {M μ pc T ℓ}
      ------------------------------------------------- RefStatic
    → ref⟦ ℓ ⟧ T M ∣ μ ∣ pc —→ ref✓⟦ ℓ ⟧ T M ∣ μ

  ref?-ok : ∀ {M μ pc T ℓ}
    → pc ≼ ℓ
      ------------------------------------------------- RefNSUSuccess
    → ref?⟦ ℓ ⟧ T M ∣ μ ∣ pc —→ ref✓⟦ ℓ ⟧ T M ∣ μ

  ref?-fail : ∀ {M μ pc T ℓ}
    → ¬ pc ≼ ℓ
      ------------------------------------------------- RefNSUFail
    → ref?⟦ ℓ ⟧ T M ∣ μ ∣ pc —→ error (Ref (T of l ℓ) of l low) nsu-error ∣ μ

  ref : ∀ {V μ pc n T ℓ}
    → (v : Value V)
    → a⟦ ℓ ⟧ n FreshIn μ
      -------------------------------------------------------------------------------- Ref
    → ref✓⟦ ℓ ⟧ T V ∣ μ ∣ pc —→ addr (a⟦ ℓ ⟧ n) of low ∣ cons-μ (a⟦ ℓ ⟧ n) V v μ

  deref : ∀ {V μ pc v n ℓ ℓ̂}
    → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      --------------------------------------------------------------------- Deref
    → ! (addr (a⟦ ℓ̂ ⟧ n) of ℓ) ∣ μ ∣ pc —→ prot (ℓ̂ ⋎ ℓ) V ∣ μ

  assign-static : ∀ {L M μ pc}
      ------------------------------------------------------- AssignStatic
    → L := M ∣ μ ∣ pc —→ L :=✓ M ∣ μ

  assign?-ok : ∀ {M μ pc n ℓ ℓ̂}
    → pc ≼ ℓ̂
      ----------------------------------------------------------------------------- AssignNSUSuccess
    → (addr (a⟦ ℓ̂ ⟧ n) of ℓ) :=? M ∣ μ ∣ pc —→ (addr (a⟦ ℓ̂ ⟧ n) of ℓ) :=✓ M ∣ μ

  assign?-fail : ∀ {M μ pc n ℓ ℓ̂}
    → ¬ pc ≼ ℓ̂
      ----------------------------------------------------------------------------- AssignNSUFail
    → (addr (a⟦ ℓ̂ ⟧ n) of ℓ) :=? M ∣ μ ∣ pc —→ error (` Unit of l low) nsu-error ∣ μ

  assign : ∀ {V μ pc n ℓ ℓ̂}
    → (v : Value V)
      ---------------------------------------------------------------------------------------------- Assign
    → (addr (a⟦ ℓ̂ ⟧ n) of ℓ) :=✓ V ∣ μ ∣ pc —→ $ tt of low ∣ cons-μ (a⟦ ℓ̂ ⟧ n) V v μ

  -- {- Reduction rules about casts, active and inert: -}
  -- cast : ∀ {A B V M μ pc} {c : Cast A ⇒ B}
  --   → Value V → Active c
  --   → ApplyCast V , c ↝ M
  --     -------------------------------------------------- Cast
  --   → V ⟨ c ⟩ ∣ μ ∣ pc —→ M ∣ μ

  -- fun-cast : ∀ {V W μ pc A B C D gc₁ gc₂ g₁ g₂} {c : Cast (⟦ gc₁ ⟧ A ⇒ B of g₁) ⇒ (⟦ gc₂ ⟧ C ⇒ D of g₂)}
  --   → Value V → Value W
  --   → (i : Inert c)
  --     ---------------------------------------------------------------- FunCast
  --   → (V ⟨ c ⟩) · W ∣ μ ∣ pc —→ elim-fun-proxy V W i pc ∣ μ

  -- deref-cast : ∀ {V μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
  --   → Value V
  --   → Inert c
  --     ------------------------------------------------------ DerefCast
  --   → ! (V ⟨ c ⟩) ∣ μ ∣ pc —→ ! V ⟨ out/c c ⟩ ∣ μ

  -- assign?-cast : ∀ {V M μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
  --   → Value V
  --   → (i : Inert c)
  --     ----------------------------------------------------------------------------- AssignNSUCast
  --   → (V ⟨ c ⟩) :=? M ∣ μ ∣ pc —→ elim-ref-proxy V M i _:=?_ ∣ μ

  -- assign-cast : ∀ {V W μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
  --   → Value V → Value W
  --   → (i : Inert c)
  --     --------------------------------------------------------------------------------------------- AssignCast
  --   → (V ⟨ c ⟩) :=✓ W ∣ μ ∣ pc —→ elim-ref-proxy V W i _:=✓_ {- V := (W ⟨ in/c c ⟩) -} ∣ μ

  β-cast-pc : ∀ {V μ pc g}
    → Value V
      ------------------------------------- CastPC
    → cast-pc g V ∣ μ ∣ pc —→ V ∣ μ
