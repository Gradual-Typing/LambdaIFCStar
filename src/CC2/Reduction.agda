module CC2.Reduction where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common.Utils
open import CoercionExpr.SecurityLevel
open import LabelExpr.Stamping
open import CC2.Statics
open import CC2.Frame public
open import CC2.Stamping
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


  prot-ctx : ∀ {M M′ μ μ′ PC PC′ A ℓ} {vc}
    →                M ∣ μ ∣ PC  —→ M′ ∣ μ′
      ------------------------------------------------------------- ProtectContext
    → prot PC vc ℓ M A ∣ μ ∣ PC′ —→ prot PC vc ℓ M′ A ∣ μ′


  prot-val : ∀ {V μ PC PC′ A ℓ} {vc}
    → (v  : Value V)
      ------------------------------------------------------------- ProtectValue
    → prot PC vc ℓ V A ∣ μ ∣ PC′ —→ stamp-val V v A ℓ ∣ μ


  prot-blame : ∀ {μ PC PC′ A ℓ p} {vc}
      ------------------------------------------------------------- ProtectBlame
    → prot PC vc ℓ (blame p) A ∣ μ ∣ PC′ —→ blame p ∣ μ


  cast : ∀ {A B V M} {c : Cast A ⇒ B} {μ PC}
    → Value V
    → V ⟨ c ⟩ —→ M
      --------------------------------- Cast
    → V ⟨ c ⟩ ∣ μ ∣ PC —→ M ∣ μ


  β : ∀ {N V A B ℓ μ PC}
    → (v  : Value V)
    → (vc : LVal PC)
      --------------------------------------------------------------- App
    → app (ƛ N) V A B ℓ ∣ μ ∣ PC —→
         prot (stampₑ PC vc ℓ) (stampₑ-LVal vc) ℓ (N [ V ]) B ∣ μ


  app-cast : ∀ {N V W A B C D gc₁ gc₂ ℓ₁ ℓ₂} {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
               {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC PC′}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → (stampₑ PC vc ℓ₂) ⟪ d̅ ⟫ —↠ₑ PC′
    → (vc′ : LVal PC′)
    → V ⟨ c ⟩ —↠ W
    → Value W
      ---------------------------------------------------------------------------- AppCast
    → app (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D ℓ₂ ∣ μ ∣ PC —→
         prot PC′ vc′ ℓ₂ ((N [ W ]) ⟨ d ⟩) D ∣ μ


  app-blame-pc : ∀ {N V A B C D gc₁ gc₂ ℓ₁ ℓ₂} {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
                   {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC p}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → (stampₑ PC vc ℓ₂) ⟪ d̅ ⟫ —↠ₑ bl p
      ---------------------------------------------------------------------------- AppBlamePC
    → app (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D ℓ₂ ∣ μ ∣ PC —→ blame p ∣ μ


  app-blame : ∀ {N V A B C D gc₁ gc₂ ℓ₁ ℓ₂} {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
                {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC PC′ p}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → (stampₑ PC vc ℓ₂) ⟪ d̅ ⟫ —↠ₑ PC′
    → (vc′ : LVal PC′)
    → V ⟨ c ⟩ —↠ blame p
      ---------------------------------------------------------------------------- AppBlame
    → app (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D ℓ₂ ∣ μ ∣ PC —→ blame p ∣ μ


  app⋆-cast : ∀ {N V W A B C T gc ℓ} {d̅ : CExpr ⋆ ⇒ gc} {c̅ₙ : CExpr l ℓ ⇒ ⋆}
                {c : Cast C ⇒ A} {d : Cast B ⇒ T of ⋆} {μ PC PC′}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stamp!ₑ PC vc ℓ′) ⟪ d̅ ⟫ —↠ₑ PC′
    → (vc′ : LVal PC′)
    → V ⟨ c ⟩ —↠ W
    → Value W
      -------------------------------------------------------------------------- App⋆Cast
    → app⋆ (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C T ∣ μ ∣ PC —→
         prot PC′ vc′ ℓ′ ((N [ W ]) ⟨ d ⟩) (T of ⋆) ∣ μ


  app⋆-blame-pc : ∀ {N V A B C T gc ℓ} {d̅ : CExpr ⋆ ⇒ gc} {c̅ₙ : CExpr l ℓ ⇒ ⋆}
                    {c : Cast C ⇒ A} {d : Cast B ⇒ T of ⋆} {μ PC p}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stamp!ₑ PC vc ℓ′) ⟪ d̅ ⟫ —↠ₑ bl p
      --------------------------------------------------------------------------- App⋆BlamePC
    → app⋆ (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C T ∣ μ ∣ PC —→ blame p ∣ μ


  app⋆-blame : ∀ {N V A B C T gc ℓ} {d̅ : CExpr ⋆ ⇒ gc} {c̅ₙ : CExpr l ℓ ⇒ ⋆}
                 {c : Cast C ⇒ A} {d : Cast B ⇒ T of ⋆} {μ PC PC′ p}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stamp!ₑ PC vc ℓ′) ⟪ d̅ ⟫ —↠ₑ PC′
    → (vc′ : LVal PC′)
    → V ⟨ c ⟩ —↠ blame p
      --------------------------------------------------------------------------- App⋆Blame
    → app⋆ (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C T ∣ μ ∣ PC —→ blame p ∣ μ


  β-if-true : ∀ {A ℓ M N μ PC}
    → (vc : LVal PC)
      ------------------------------------------------------------------------------------- IfTrue
    → if ($ true) A ℓ M N ∣ μ ∣ PC —→ prot (stampₑ PC vc ℓ) (stampₑ-LVal vc) ℓ M A ∣ μ


  β-if-false : ∀ {A ℓ M N μ PC}
    → (vc : LVal PC)
      ------------------------------------------------------------------------------------- IfFalse
    → if ($ false) A ℓ M N ∣ μ ∣ PC —→ prot (stampₑ PC vc ℓ) (stampₑ-LVal vc) ℓ N A ∣ μ


  if-true-cast : ∀ {A M N μ PC}
    → (vc : LVal PC)
      ------------------------------------------------------------------------ IfTrueCast
    → if ($ true ⟨ cast (id Bool) (id (l low) ⨾ ↑) ⟩) A high M N ∣ μ ∣ PC —→
         prot (stampₑ PC vc high) (stampₑ-LVal vc) high M A ∣ μ


  if-false-cast : ∀ {A M N μ PC}
    → (vc : LVal PC)
      ------------------------------------------------------------------------ IfFalseCast
    → if ($ false ⟨ cast (id Bool) (id (l low) ⨾ ↑) ⟩) A high M N ∣ μ ∣ PC —→
         prot (stampₑ PC vc high) (stampₑ-LVal vc) high N A ∣ μ


  if⋆-true-cast : ∀ {T ℓ M N} {c̅ₙ : CExpr l ℓ ⇒ ⋆} {μ PC}
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
      ------------------------------------------------------------------ If⋆TrueCast
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       if⋆ ($ true ⟨ cast (id Bool) c̅ₙ ⟩) T M N ∣ μ ∣ PC —→
         prot (stamp!ₑ PC vc ℓ′) (stamp!ₑ-LVal vc) ℓ′ M (T of ⋆) ∣ μ


  if⋆-false-cast : ∀ {T ℓ M N} {c̅ₙ : CExpr l ℓ ⇒ ⋆} {μ PC}
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
      ------------------------------------------------------------------ If⋆FalseCast
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       if⋆ ($ false ⟨ cast (id Bool) c̅ₙ ⟩) T M N ∣ μ ∣ PC —→
         prot (stamp!ₑ PC vc ℓ′) (stamp!ₑ-LVal vc) ℓ′ N (T of ⋆) ∣ μ


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


  ref?-blame-pc : ∀ {ℓ V p q μ PC}
    → (v : Value V)
    → PC ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l p ⟫ —↠ₑ bl q
      -------------------------------------------------------------------- Ref?BlamePC
    → ref?⟦ ℓ ⟧ V p ∣ μ ∣ PC —→ blame q ∣ μ


  deref : ∀ {n T ℓ̂ ℓ V v μ PC}
    → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      -------------------------------------------------------------- Deref
    → ! (addr n) (T of l ℓ̂) ℓ ∣ μ ∣ PC —→
         prot (l high) v-l ℓ V (T of l ℓ̂) ∣ μ


  deref-cast : ∀ {A T ℓ̂ ℓ₁ ℓ₂ V v n} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
                 {c : Cast A ⇒ T of l ℓ̂} {d : Cast T of l ℓ̂ ⇒ A} {μ PC}
    → (𝓋 : CVal c̅ₙ)
    → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      -------------------------------------------------------------- DerefCast
    → ! (addr n ⟨ cast (ref c d) c̅ₙ ⟩) A ℓ₂ ∣ μ ∣ PC —→
         prot (l high) v-l ℓ₂ (V ⟨ d ⟩) A ∣ μ


  deref⋆-cast : ∀ {S T ℓ̂ ℓ V v n} {c̅ₙ : CExpr l ℓ ⇒ ⋆}
                 {c : Cast S of ⋆ ⇒ T of l ℓ̂} {d : Cast T of l ℓ̂ ⇒ S of ⋆} {μ PC}
    → (𝓋 : CVal c̅ₙ)
    → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      ---------------------------------------------------------------------- Deref⋆Cast
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       !⋆ (addr n ⟨ cast (ref c d) c̅ₙ ⟩) S ∣ μ ∣ PC —→
           prot (l high) v-l ℓ′ (V ⟨ d ⟩) (S of ⋆) ∣ μ


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


  assign?-cast : ∀ {S T ℓ̂ ĝ ℓ V W n} {c̅ₙ : CExpr l ℓ ⇒ ⋆}
              {c : Cast T of ĝ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of ĝ} {μ PC PC′ p}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stamp!ₑ PC vc ℓ′) ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ PC′
    → LVal PC′
    → V ⟨ c ⟩ —↠ W
    → (w : Value W)
      ---------------------------------------------------------------------- Assign?Cast
    → assign? (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ĝ p ∣ μ ∣ PC —→
         $ tt ∣ cons-μ (a⟦ ℓ̂ ⟧ n) W w μ


  assign?-cast-blame-pc : ∀ {S T ℓ̂ ĝ ℓ V n} {c̅ₙ : CExpr l ℓ ⇒ ⋆}
       {c : Cast T of ĝ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of ĝ} {μ PC p q}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stamp!ₑ PC vc ℓ′) ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ bl q
      ------------------------------------------------------------------------------------ Assign?CastBlamePC
    → assign? (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ĝ p ∣ μ ∣ PC —→ blame q ∣ μ


  assign?-cast-blame : ∀ {S T ℓ̂ ĝ ℓ V n} {c̅ₙ : CExpr l ℓ ⇒ ⋆}
              {c : Cast T of ĝ ⇒ S of l ℓ̂} {d : Cast S of l ℓ̂ ⇒ T of ĝ} {μ PC PC′ p q}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stamp!ₑ PC vc ℓ′) ⟪ coerceₗ {⋆} {l ℓ̂} ≾-⋆l p ⟫ —↠ₑ PC′
    → LVal PC′
    → V ⟨ c ⟩ —↠ blame q
      ----------------------------------------------------------------------------------- Assign?CastBlame
    → assign? (addr n ⟨ cast (ref c d) c̅ₙ ⟩) V T ĝ p ∣ μ ∣ PC —→ blame q ∣ μ


Value⌿→ : ∀ {V M μ μ′ PC}
  → Value V
  → ¬ (V ∣ μ ∣ PC —→ M ∣ μ′)
Value⌿→ (V-raw v) (ξ {F = F} r) = plug-not-raw F v
Value⌿→ (V-raw v) (ξ-blame {F = F}) = plug-not-raw F v
Value⌿→ V-● r = ●⌿→ r refl
  where
  ●⌿→ : ∀ {M N μ μ′ PC} → (M ∣ μ ∣ PC —→ N ∣ μ′) → M ≡ ● → Bot
  ●⌿→ (ξ       {F = F} r) eq = contradiction eq (plug-not-● F)
  ●⌿→ (ξ-blame {F = F})   eq = contradiction eq (plug-not-● F)
Value⌿→ (V-cast v i) r = ir⌿→ r refl v i
  where
  ir⌿→ : ∀ {A B} {M N V μ μ′ PC} {c : Cast A ⇒ B}
    → (M ∣ μ ∣ PC —→ N ∣ μ′)
    → M ≡ V ⟨ c ⟩
    → RawValue V → Irreducible c → Bot
  ir⌿→ (ξ {F = □⟨ c ⟩} r) refl v i = Value⌿→ (V-raw v) r
  ir⌿→ (ξ-blame {F = □⟨ c ⟩}) refl () i
  ir⌿→ (cast v† (cast x (_ —→ₗ⟨ r ⟩ _) x₂)) refl v (ir-base 𝓋 _) = CVal⌿→ 𝓋 r
  ir⌿→ (cast v† (cast x (_ —→ₗ⟨ r ⟩ _) x₂)) refl v (ir-ref 𝓋) = CVal⌿→ 𝓋 r
  ir⌿→ (cast v† (cast x (_ —→ₗ⟨ r ⟩ _) x₂)) refl v (ir-fun 𝓋) = CVal⌿→ 𝓋 r
  ir⌿→ (cast v† (cast-blame x (_ —→ₗ⟨ r ⟩ _))) refl v (ir-base 𝓋 _) = CVal⌿→ 𝓋 r
  ir⌿→ (cast v† (cast-blame x (_ —→ₗ⟨ r ⟩ _))) refl v (ir-ref 𝓋) = CVal⌿→ 𝓋 r
  ir⌿→ (cast v† (cast-blame x (_ —→ₗ⟨ r ⟩ _))) refl v (ir-fun 𝓋) = CVal⌿→ 𝓋 r
  ir⌿→ (cast v† cast-id) refl v (ir-base _ ℓ≢ℓ) = contradiction refl ℓ≢ℓ
  ir⌿→ (cast v† (cast-comp x x₁)) refl ()


Result⌿→ : ∀ {M N μ μ′ PC}
  → Result M
  → ¬ (M ∣ μ ∣ PC —→ N ∣ μ′)
Result⌿→ (success v) V→N = contradiction V→N (Value⌿→ v)
Result⌿→ fail M→N = bl⌿→ M→N refl
  where
  bl⌿→ : ∀ {M N μ μ′ PC p} → (M ∣ μ ∣ PC —→ N ∣ μ′) → M ≡ blame p → Bot
  bl⌿→ (ξ       {F = F} r) eq = plug-not-bl F eq
  bl⌿→ (ξ-blame {F = F})   eq = plug-not-bl F eq
