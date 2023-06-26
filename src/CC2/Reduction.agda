module CC2.Reduction where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common.Utils
open import CoercionExpr.SecurityLevel
open import CC2.Statics
open import CC2.Frame public
open import Memory.Heap Term Value


open import CC2.CastReduction public

infix 2 _∣_∣_—→_∣_

data _∣_∣_—→_∣_ : Term → Heap → LExpr → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ PC}
    →        M ∣ μ ∣ PC —→ M′        ∣ μ′
      -------------------------------------------------- ξ
    → plug M F ∣ μ ∣ PC —→ plug M′ F ∣ μ′

  ξ-blame : ∀ {F μ PC p}
      ------------------------------------------------------ ξ-blame
    → plug (blame p) F ∣ μ ∣ PC —→ blame p ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ PC PC′ A ℓ} {v}
    →                         M ∣ μ ∣ PC  —→ M′ ∣ μ′
      ---------------------------------------------------------------------------- ProtectContext
    → prot PC (success v) ℓ M A ∣ μ ∣ PC′ —→ prot PC (success v) ℓ M′ A ∣ μ′

  prot-val : ∀ {Σ gc ℓv V μ PC PC′ A ℓ} {vc}
    → (v  : Value V)
    → (⊢V : [] ; Σ ; gc ; ℓv ⊢ V ⇐ A)
      ------------------------------------------------------------------------ ProtectValue
    → prot PC (success vc) ℓ V A ∣ μ ∣ PC′ —→ stamp-val V v ⊢V ℓ ∣ μ

  prot-blame : ∀ {μ PC PC′ A ℓ p} {v}
      ------------------------------------------------------------------------ ProtectBlame
    → prot PC (success v) ℓ (blame p) A ∣ μ ∣ PC′ —→ blame p ∣ μ

  prot-blame-pc : ∀ {M μ PC A ℓ p}
      ------------------------------------------------------------------ ProtectBlamePC
    → prot (bl p) fail ℓ M A ∣ μ ∣ PC —→ blame p ∣ μ

  cast : ∀ {A B V M} {c : Cast A ⇒ B} {μ PC}
    → Value V
    → V ⟨ c ⟩ —→ M
      --------------------------------- Cast
    → V ⟨ c ⟩ ∣ μ ∣ PC —→ M ∣ μ

  β : ∀ {N V A B ℓ μ PC}
    → (v  : Value V)
    → (vc : LVal PC)
      ------------------------------------------------------------------------------ App
    → app (ƛ N) V A B ℓ ∣ μ ∣ PC —→
         prot (stampₑ PC vc ℓ) (success (stampₑ-LVal vc)) ℓ (N [ V ]) B ∣ μ

  β-app! : ∀ {N V A B ℓ μ PC PC′} {gc}
    → (v  : Value V)
    → (vc : LVal PC)
    → ⊢ PC ⇐ gc
    → (stampₑ PC vc ℓ) ⟪ coerce (gc ⋎̃ l ℓ) ⇒⋆ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      ------------------------------------------------------------------------------ App!
    → app! (ƛ N) V A B (l ℓ) ∣ μ ∣ PC —→ prot PC′ r ℓ (N [ V ]) B ∣ μ

  app-cast : ∀ {N V W A B C D gc₁ gc₂ ℓ₁ ℓ₂} {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
               {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC PC′}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → (stampₑ PC vc ℓ₂) ⟪ d̅ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
    → V ⟨ c ⟩ —↠ W
    → Value W
      ---------------------------------------------------------------------------- AppCast
    → app (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D ℓ₂ ∣ μ ∣ PC —→
         prot PC′ r ℓ₂ ((N [ W ]) ⟨ d ⟩) D ∣ μ

  app-blame : ∀ {N V A B C D gc₁ gc₂ ℓ₁ ℓ₂} {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
                {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC p}
    → (v  : Value V)
    → (𝓋  : CVal c̅ₙ)
    → V ⟨ c ⟩ —↠ blame p
      ---------------------------------------------------------------------------- AppBlame
    → app (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D ℓ₂ ∣ μ ∣ PC —→ blame p ∣ μ

  app!-cast : ∀ {N V W A B C D gc gc′ ℓ g} {d̅ : CExpr ⋆ ⇒ gc} {c̅ₙ : CExpr l ℓ ⇒ g}
                {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC PC′}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → ⊢ PC ⇐ gc′
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stampₑ PC vc ℓ′) ⟪ coerce (gc′ ⋎̃ l ℓ′) ⇒⋆ ⟫ ⟪ d̅ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
    → V ⟨ c ⟩ —↠ W
    → Value W
      ---------------------------------------------------------------------------- App!Cast
    → app! (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D g ∣ μ ∣ PC —→
         prot PC′ r ℓ′ ((N [ W ]) ⟨ d ⟩) D ∣ μ

  app!-blame : ∀ {N V A B C D gc ℓ g} {d̅ : CExpr ⋆ ⇒ gc} {c̅ₙ : CExpr l ℓ ⇒ g}
                 {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC p}
    → (v  : Value V)
    → (𝓋  : CVal c̅ₙ)
    → V ⟨ c ⟩ —↠ blame p
      ---------------------------------------------------------------------------- App!Blame
    → app! (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D g ∣ μ ∣ PC —→ blame p ∣ μ

  β-if-true : ∀ {A ℓ M N μ PC}
    → (v : LVal PC)
      ------------------------------------------------------------------------------------- IfTrue
    → if ($ true) A ℓ M N ∣ μ ∣ PC —→ prot (stampₑ PC v ℓ) (success (stampₑ-LVal v)) ℓ M A ∣ μ

  β-if-false : ∀ {A ℓ M N μ PC}
    → (v : LVal PC)
      ------------------------------------------------------------------------------------- IfFalse
    → if ($ false) A ℓ M N ∣ μ ∣ PC —→ prot (stampₑ PC v ℓ) (success (stampₑ-LVal v)) ℓ N A ∣ μ

  β-if!-true : ∀ {A ℓ gc M N μ PC PC′}
    → (v : LVal PC)
    → ⊢ PC ⇐ gc
    → stampₑ PC v ℓ ⟪ coerce (gc ⋎̃ l ℓ) ⇒⋆ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      -------------------------------------------------------------------- If!True
    → if! ($ true) A (l ℓ) M N ∣ μ ∣ PC —→ prot PC′ r ℓ M A ∣ μ

  β-if!-false : ∀ {A ℓ gc M N μ PC PC′}
    → (v : LVal PC)
    → ⊢ PC ⇐ gc
    → stampₑ PC v ℓ ⟪ coerce (gc ⋎̃ l ℓ) ⇒⋆ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      --------------------------------------------------------------------- If!False
    → if! ($ false) A (l ℓ) M N ∣ μ ∣ PC —→ prot PC′ r ℓ N A ∣ μ

  if-true-cast : ∀ {A M N μ PC}
    → (v : LVal PC)
      ------------------------------------------------------------------------ IfTrueCast
    → if ($ true ⟨ cast (id Bool) (id (l low) ⨾ ↑) ⟩) A high M N ∣ μ ∣ PC —→
         prot (stampₑ PC v high) (success (stampₑ-LVal v)) high M A ∣ μ

  if-false-cast : ∀ {A M N μ PC}
    → (v : LVal PC)
      ------------------------------------------------------------------------ IfFalseCast
    → if ($ false ⟨ cast (id Bool) (id (l low) ⨾ ↑) ⟩) A high M N ∣ μ ∣ PC —→
         prot (stampₑ PC v high) (success (stampₑ-LVal v)) high N A ∣ μ

  if!-true-cast : ∀ {A ℓ g gc M N} {c̅ₙ : CExpr l ℓ ⇒ g} {μ PC PC′}
    → (v : LVal PC)
    → (𝓋 : CVal c̅ₙ)
    → l ℓ ≢ g
    → ⊢ PC ⇐ gc
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       stampₑ PC v ℓ′ ⟪ coerce (gc ⋎̃ l ℓ′) ⇒⋆ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      ------------------------------------------------------------------------------ If!TrueCast
    → if! ($ true ⟨ cast (id Bool) c̅ₙ ⟩) A g M N ∣ μ ∣ PC —→ prot PC′ r ℓ′ M A ∣ μ

  if!-false-cast : ∀ {A ℓ g gc M N} {c̅ₙ : CExpr l ℓ ⇒ g} {μ PC PC′}
    → (v : LVal PC)
    → (𝓋 : CVal c̅ₙ)
    → l ℓ ≢ g
    → ⊢ PC ⇐ gc
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       stampₑ PC v ℓ′ ⟪ coerce (gc ⋎̃ l ℓ′) ⇒⋆ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      ------------------------------------------------------------------------------ If!FalseCast
    → if! ($ false ⟨ cast (id Bool) c̅ₙ ⟩) A g M N ∣ μ ∣ PC —→ prot PC′ r ℓ′ N A ∣ μ

  β-let : ∀ {V A N μ PC}
    → Value V
      ----------------------------------------------- Let
    → `let V A N ∣ μ ∣ PC —→ N [ V ] ∣ μ

  ref : ∀ {ℓ V n μ PC}
    → (v : Value V)
    → a⟦ ℓ ⟧ n FreshIn μ
      -------------------------------------------------------------------- Ref
    → ref⟦ ℓ ⟧ V ∣ μ ∣ PC —→ addr n ∣ cons-μ (a⟦ ℓ ⟧ n) V v μ

  ref? : ∀ {ℓ V n p μ PC PC′}
    → (v : Value V)
    → a⟦ ℓ ⟧ n FreshIn μ
    → PC ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l p ⟫ —↠ₑ PC′
    → LVal PC′
      -------------------------------------------------------------------- Ref?
    → ref?⟦ ℓ ⟧ V p ∣ μ ∣ PC —→ addr n ∣ cons-μ (a⟦ ℓ ⟧ n) V v μ

  ref?-blame : ∀ {ℓ V p q μ PC}
    → (v : Value V)
    → PC ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l p ⟫ —↠ₑ bl q
      -------------------------------------------------------------------- Ref?Blame
    → ref?⟦ ℓ ⟧ V p ∣ μ ∣ PC —→ blame q ∣ μ

  deref : ∀ {n T ℓ̂ ℓ V v μ PC}
    → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      -------------------------------------------------------------- Deref
    → ! (addr n) (T of l ℓ̂) (l ℓ) ∣ μ ∣ PC —→
         prot (l high) (success v-l) ℓ V (T of l ℓ̂) ∣ μ

  deref-cast : ∀ {A T ℓ̂ ℓ g V v n} {c̅ₙ : CExpr l ℓ ⇒ g}
                 {c : Cast A ⇒ T of l ℓ̂} {d : Cast T of l ℓ̂ ⇒ A} {μ PC}
    → (𝓋 : CVal c̅ₙ)
    → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      -------------------------------------------------------------- DerefCast
    → ! (addr n ⟨ cast (ref c d) c̅ₙ ⟩) A g ∣ μ ∣ PC —→
         prot (l high) (success v-l) (∥ c̅ₙ ∥ₗ 𝓋) (V ⟨ d ⟩) A ∣ μ

  β-assign : ∀ {T ℓ̂ ℓ V n} {μ PC}
    → (v : Value V)
      ---------------------------------------------------------------------- Assign
    → assign (addr n) V T ℓ̂ ℓ ∣ μ ∣ PC —→ $ tt ∣ cons-μ (a⟦ ℓ̂ ⟧ n) V v μ

  assign-cast : ∀ {S T ℓ̂₁ ℓ̂₂ ℓ₁ ℓ₂ V W n} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
                  {c : Cast T of l ℓ̂₂ ⇒ S of l ℓ̂₁} {d : Cast S of l ℓ̂₁ ⇒ T of l ℓ̂₂} {μ PC}
    → (v : Value V)
    → (𝓋 : CVal c̅ₙ)
    → V ⟨ c ⟩ —↠ W
    → (w : Value W)
      ---------------------------------------------------------------------- AssignCast
    → assign (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ℓ̂₂ ℓ₂ ∣ μ ∣ PC —→
         $ tt ∣ cons-μ (a⟦ ℓ̂₁ ⟧ n) W w μ

  assign-blame : ∀ {S T ℓ̂₁ ℓ̂₂ ℓ₁ ℓ₂ V n} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
                {c : Cast T of l ℓ̂₂ ⇒ S of l ℓ̂₁} {d : Cast S of l ℓ̂₁ ⇒ T of l ℓ̂₂} {μ PC p}
    → (v : Value V)
    → (𝓋 : CVal c̅ₙ)
    → V ⟨ c ⟩ —↠ blame p
      ---------------------------------------------------------------------------- AssignBlame
    → assign (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ℓ̂₂ ℓ₂ ∣ μ ∣ PC —→ blame p ∣ μ

  assign?-cast : ∀ {S T ℓ̂ ĝ ℓ g gc V W n} {c̅ₙ : CExpr l ℓ ⇒ g}
              {c : Cast T of ĝ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of ĝ} {μ PC PC′ p}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → ⊢ PC ⇐ gc
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stampₑ PC vc ℓ) ⟪ coerce gc ⋎̃ l ℓ′ ⇒⋆ ⟫ ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ PC′
    → LVal PC′
    → V ⟨ c ⟩ —↠ W
    → (w : Value W)
      ---------------------------------------------------------------------- Assign?
    → assign? (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ĝ g p ∣ μ ∣ PC —→
         $ tt ∣ cons-μ (a⟦ ℓ̂ ⟧ n) W w μ

  assign?-blame-pc : ∀ {S T ℓ̂ ĝ ℓ g gc V n} {c̅ₙ : CExpr l ℓ ⇒ g}
       {c : Cast T of ĝ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of ĝ} {μ PC p}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → ⊢ PC ⇐ gc
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stampₑ PC vc ℓ) ⟪ coerce gc ⋎̃ l ℓ′ ⇒⋆ ⟫ ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ bl p
      --------------------------------------------------------------------------- Assign?BlamePC
    → assign? (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ĝ g p ∣ μ ∣ PC —→ blame p ∣ μ

  assign?-blame : ∀ {S T ℓ̂ ĝ ℓ g gc V n} {c̅ₙ : CExpr l ℓ ⇒ g}
              {c : Cast T of ĝ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of ĝ} {μ PC PC′ p q}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → ⊢ PC ⇐ gc
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stampₑ PC vc ℓ) ⟪ coerce gc ⋎̃ l ℓ′ ⇒⋆ ⟫ ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ PC′
    → LVal PC′
    → V ⟨ c ⟩ —↠ blame q
      ---------------------------------------------------------------------------- Assign?Blame
    → assign? (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ĝ g p ∣ μ ∣ PC —→ blame q ∣ μ
