module CC2.BigStep where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils
open import CoercionExpr.SecurityLevel
open import CC2.Statics
open import Memory.Heap Term Value


infix 2 _∣_⊢_⇓_∣_
data _∣_⊢_⇓_∣_ : Heap → LExpr → (M V : Term) → Heap → Set

postulate
  ⇓-value : ∀ {μ μ′ pc M V} → μ ∣ pc ⊢ M ⇓ V ∣ μ′ → Value V

{- only consider evaluation to values -}
data _∣_⊢_⇓_∣_ where

  ⇓-val : ∀ {μ PC V}
    → Value V
      --------------------------- ⇓-Val
    → μ ∣ PC ⊢ V ⇓ V ∣ μ

  ⇓-app : ∀ {μ μ₁ μ₂ μ₃ PC L M N V W A B ℓ}
    → μ  ∣ PC     ⊢ L ⇓ ƛ N ∣ μ₁
    → μ₁ ∣ PC     ⊢ M ⇓ V   ∣ μ₂
    → (vc : LVal PC)
    → (⇓W : μ₂ ∣ stampₑ PC vc ℓ ⊢ N [ V ] ⇓ W ∣ μ₃)
      ---------------------------------------------------------------------- ⇓-App
    → μ  ∣ PC     ⊢ app L M A B ℓ ⇓ stamp-val W (⇓-value ⇓W) B ℓ ∣ μ₃

  ⇓-app-cast : ∀ {μ μ₁ μ₂ μ₃ μ₄ PC PC′ L M N V V′ W A B C D gc₁ gc₂ ℓ₁ ℓ₂}
                  {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
                  {c : Cast C ⇒ A} {d : Cast B ⇒ D}
    → μ  ∣ PC     ⊢ L ⇓ ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩ ∣ μ₁
    → μ₁ ∣ PC     ⊢ M ⇓ V   ∣ μ₂
    → μ₂ ∣ PC     ⊢ V ⟨ c ⟩ ⇓ V′ ∣ μ₃
    → (vc  : LVal PC )
    → stampₑ PC vc ℓ₂ ⟪ d̅ ⟫ —↠ₑ PC′
    → (vc′ : LVal PC′)
    → (⇓W : μ₃ ∣ PC′ ⊢ (N [ V′ ]) ⟨ d ⟩ ⇓ W ∣ μ₄)
      ---------------------------------------------------------------------- ⇓-AppCast
    → μ  ∣ PC     ⊢ app L M C D ℓ₂ ⇓ stamp-val W (⇓-value ⇓W) D ℓ₂ ∣ μ₄

--   ⇓-if-true : ∀ {μ μ₁ μ₂ pc L M N V A ℓ}
--     → μ  ∣ pc     ⊢ L ⇓ $ true of ℓ ∣ μ₁
--     → (⇓V : μ₁ ∣ pc ⋎ ℓ ⊢ M ⇓ V ∣ μ₂)
--       ---------------------------------------------------------------------- IfTrue
--     → μ  ∣ pc     ⊢ if L A M N ⇓ stamp-val V (⇓-value ⇓V) ℓ ∣ μ₂

--   ⇓-if-false : ∀ {μ μ₁ μ₂ pc L M N V A ℓ}
--     → μ  ∣ pc     ⊢ L ⇓ $ false of ℓ ∣ μ₁
--     → (⇓V : μ₁ ∣ pc ⋎ ℓ ⊢ N ⇓ V ∣ μ₂)
--       ---------------------------------------------------------------------- IfFalse
--     → μ  ∣ pc     ⊢ if L A M N ⇓ stamp-val V (⇓-value ⇓V) ℓ ∣ μ₂

--   ⇓-let : ∀ {μ μ₁ μ₂ pc M N V W}
--     → μ  ∣ pc ⊢ M        ⇓ V ∣ μ₁
--     → μ₁ ∣ pc ⊢ N [ V ]  ⇓ W ∣ μ₂
--       ----------------------------------------- Let
--     → μ  ∣ pc ⊢ `let M N ⇓ W ∣ μ₂

--   ⇓-ref? : ∀ {μ μ₁ pc M V n ℓ}
--     → (⇓V : μ ∣ pc ⊢ M ⇓ V ∣ μ₁)
--     → a⟦ ℓ ⟧ n FreshIn μ₁
--     → pc ≼ ℓ
--       -------------------------------------------------------------------------------------- RefNSU
--     → μ ∣ pc ⊢ ref?⟦ ℓ ⟧ M ⇓ addr a⟦ ℓ ⟧ n of low ∣ cons-μ (a⟦ ℓ ⟧ n) V (⇓-value ⇓V) μ₁

--   ⇓-ref : ∀ {μ μ₁ pc M V n ℓ}
--     → (⇓V : μ ∣ pc ⊢ M ⇓ V ∣ μ₁)
--     → a⟦ ℓ ⟧ n FreshIn μ₁
--       -------------------------------------------------------------------------------------- Ref
--     → μ ∣ pc ⊢ ref⟦ ℓ ⟧ M ⇓ addr a⟦ ℓ ⟧ n of low ∣ cons-μ (a⟦ ℓ ⟧ n) V (⇓-value ⇓V) μ₁

--   ⇓-deref : ∀ {μ μ₁ pc M V v n ℓ ℓ̂}
--     → μ ∣ pc ⊢ M ⇓ addr a⟦ ℓ̂ ⟧ n of ℓ ∣ μ₁
--     → lookup-μ μ₁ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
--       ---------------------------------------------------------------------------- Deref
--     → μ ∣ pc ⊢ ! M ⇓ stamp-val V v (ℓ̂ ⋎ ℓ) ∣ μ₁

--   ⇓-assign? : ∀ {μ μ₁ μ₂ pc L M V n ℓ ℓ̂}
--     → μ  ∣ pc ⊢ L ⇓ addr a⟦ ℓ̂ ⟧ n of ℓ ∣ μ₁
--     → (⇓V : μ₁ ∣ pc ⊢ M ⇓ V ∣ μ₂)
--     → pc ≼ ℓ̂
--       -------------------------------------------------------------------------- AssignNSU
--     → μ ∣ pc ⊢ L :=? M ⇓ $ tt of low ∣ cons-μ (a⟦ ℓ̂ ⟧ n) V (⇓-value ⇓V) μ₂

--   ⇓-assign : ∀ {μ μ₁ μ₂ pc L M V n ℓ ℓ̂}
--     → μ  ∣ pc ⊢ L ⇓ addr a⟦ ℓ̂ ⟧ n of ℓ ∣ μ₁
--     → (⇓V : μ₁ ∣ pc ⊢ M ⇓ V ∣ μ₂)
--       -------------------------------------------------------------------------- Assign
--     → μ  ∣ pc ⊢ L := M ⇓ $ tt of low ∣ cons-μ (a⟦ ℓ̂ ⟧ n) V (⇓-value ⇓V) μ₂

--   ⇓-cast : ∀ {μ μ₁ μ₂ pc M N V W A B} {c : Cast A ⇒ B}
--     → Active c
--     → μ  ∣ pc ⊢ M ⇓ V ∣ μ₁
--     → ApplyCast V , c ↝ N
--     → μ₁ ∣ pc ⊢ N ⇓ W ∣ μ₂
--       --------------------------------------------------------- Cast
--     → μ  ∣ pc ⊢ M ⟨ c ⟩ ⇓ W ∣ μ₂

--   ⇓-if-cast-true : ∀ {μ μ₁ μ₂ μ₃ pc L M N V W A g ℓ}
--                       {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
--     → Inert c
--     → μ  ∣ pc     ⊢ L                    ⇓ $ true of ℓ ⟨ c ⟩ ∣ μ₁
--     → (⇓V : μ₁ ∣ pc ⋎ ℓ ⊢ M ⇓ V ∣ μ₂)
--       {- don't need casting PC to ⋆ in big step -}
--     → μ₂ ∣ pc     ⊢ stamp-val V (⇓-value ⇓V) ℓ ⟨ branch/c A c ⟩ ⇓ W ∣ μ₃
--       --------------------------------------------------------- IfCastTrue
--     → μ  ∣ pc     ⊢ if L A M N           ⇓ W ∣ μ₃

--   ⇓-if-cast-false : ∀ {μ μ₁ μ₂ μ₃ pc L M N V W A g ℓ}
--                        {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
--     → Inert c
--     → μ  ∣ pc     ⊢ L                    ⇓ $ false of ℓ ⟨ c ⟩ ∣ μ₁
--     → (⇓V : μ₁ ∣ pc ⋎ ℓ ⊢ N ⇓ V ∣ μ₂)
--     → μ₂ ∣ pc     ⊢ stamp-val V (⇓-value ⇓V) ℓ ⟨ branch/c A c ⟩ ⇓ W ∣ μ₃
--       --------------------------------------------------------- IfCastFalse
--     → μ  ∣ pc     ⊢ if L A M N           ⇓ W ∣ μ₃

--   ⇓-fun-cast : ∀ {μ μ₁ μ₂ μ₃ pc L M V V′ W A B C D gc₁ gc₂ g₁ g₂}
--                   {c : Cast (⟦ gc₁ ⟧ A ⇒ B of g₁) ⇒ (⟦ gc₂ ⟧ C ⇒ D of g₂)}
--     → (i : Inert c)
--     → μ  ∣ pc ⊢ L                       ⇓ V ⟨ c ⟩ ∣ μ₁
--     → μ₁ ∣ pc ⊢ M                       ⇓ W  ∣ μ₂
--     → μ₂ ∣ pc ⊢ elim-fun-proxy V W i pc ⇓ V′ ∣ μ₃
--       --------------------------------------------------------- FunCast
--     → μ  ∣ pc ⊢ L · M                   ⇓ V′ ∣ μ₃

--   ⇓-deref-cast : ∀ {μ μ₁ μ₂ pc M V W A B g₁ g₂}
--                     {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
--     → Inert c
--     → μ  ∣ pc ⊢ M               ⇓ V ⟨ c ⟩ ∣ μ₁
--     → μ₁ ∣ pc ⊢ ! V ⟨ out/c c ⟩ ⇓ W ∣ μ₂
--       --------------------------------------------------------- DerefCast
--     → μ  ∣ pc ⊢ ! M             ⇓ W ∣ μ₂

--   ⇓-assign?-cast : ∀ {μ μ₁ μ₂ pc L M V W A B g₁ g₂}
--                       {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
--     → (i : Inert c)
--     → μ  ∣ pc ⊢ L                          ⇓ V ⟨ c ⟩ ∣ μ₁
--     → μ₁ ∣ pc ⊢ elim-ref-proxy V M i _:=?_ ⇓ W ∣ μ₂
--       ----------------------------------------------------------- AssignNSUCast
--     → μ  ∣ pc ⊢ L :=? M                    ⇓ W ∣ μ₂

--   ⇓-assign-cast : ∀ {μ μ₁ μ₂ pc L M V W A B g₁ g₂}
--                      {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
--     → (i : Inert c)
--     → μ  ∣ pc ⊢ L                         ⇓ V ⟨ c ⟩ ∣ μ₁
--     → μ₁ ∣ pc ⊢ elim-ref-proxy V M i _:=_ ⇓ W ∣ μ₂
--       ----------------------------------------------------------- AssignCast
--     → μ  ∣ pc ⊢ L := M                    ⇓ W ∣ μ₂


-- {- If M ⇓ V then V is Value -}
-- ⇓-value (⇓-val v) = v
-- ⇓-value (⇓-app _ _ ⇓W) = stamp-val-value (⇓-value ⇓W)
-- ⇓-value (⇓-if-true  _ ⇓V) = stamp-val-value (⇓-value ⇓V)
-- ⇓-value (⇓-if-false _ ⇓V) = stamp-val-value (⇓-value ⇓V)
-- ⇓-value (⇓-let _ ⇓V) = ⇓-value ⇓V
-- ⇓-value (⇓-ref? _ _ _) = V-addr
-- ⇓-value (⇓-ref _ _) = V-addr
-- ⇓-value (⇓-deref {v = v} _ _) = stamp-val-value v
-- ⇓-value (⇓-assign? _ _ _) = V-const
-- ⇓-value (⇓-assign _ _) = V-const
-- ⇓-value (⇓-cast          _ _ _ ⇓V) = ⇓-value ⇓V
-- ⇓-value (⇓-if-cast-true  _ _ _ ⇓V) = ⇓-value ⇓V
-- ⇓-value (⇓-if-cast-false _ _ _ ⇓V) = ⇓-value ⇓V
-- ⇓-value (⇓-fun-cast      _ _ _ ⇓V) = ⇓-value ⇓V
-- ⇓-value (⇓-deref-cast      _ _ ⇓V) = ⇓-value ⇓V
-- ⇓-value (⇓-assign?-cast    _ _ ⇓V) = ⇓-value ⇓V
-- ⇓-value (⇓-assign-cast     _ _ ⇓V) = ⇓-value ⇓V

{- If M ⇓ V then M is not Error -}
-- error-not-⇓ : ∀ {μ μ′ pc M V} → μ ∣ pc ⊢ M ⇓ V ∣ μ′ → ¬ Err M
-- error-not-⇓ (⇓-val ()) E-error
