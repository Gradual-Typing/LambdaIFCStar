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

  cast : ∀ {Vᵣ S T g₁ g₂} {cᵣ : Castᵣ S ⇒ T} {c̅ c̅ₙ : CExpr g₁ ⇒ g₂} {μ PC}
    → RawValue Vᵣ
    → c̅ —↠ c̅ₙ
    → CVal c̅ₙ
      ---------------------------------------------------------------- Cast
    → Vᵣ ⟨ cast cᵣ c̅ ⟩ ∣ μ ∣ PC —→ Vᵣ ⟨ cast cᵣ c̅ₙ ⟩ ∣ μ

  cast-blame : ∀ {Vᵣ S T g₁ g₂} {cᵣ : Castᵣ S ⇒ T} {c̅ c̅ₙ : CExpr g₁ ⇒ g₂} {μ PC p}
    → RawValue Vᵣ
    → c̅ —↠ ⊥ g₁ g₂ p
      ----------------------------------------------------------- CastBlame
    → Vᵣ ⟨ cast cᵣ c̅ ⟩ ∣ μ ∣ PC —→ blame p ∣ μ

  cast-id : ∀ {ι g} {k : rep ι} {μ PC}
      ----------------------------------------------------------- CastId
    → $ k ⟨ cast (id ι) (id g) ⟩ ∣ μ ∣ PC —→ $ k ∣ μ

  cast-comp : ∀ {Vᵣ A B C} {cᵢ : Cast A ⇒ B} {d : Cast B ⇒ C} {μ PC}
    → RawValue Vᵣ
    → Irreducible cᵢ
      ---------------------------------------------------------- CastComposition
    → Vᵣ ⟨ cᵢ ⟩ ⟨ d ⟩ ∣ μ ∣ PC —→ Vᵣ ⟨ cᵢ ⨟ d ⟩ ∣ μ

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

  app-cast : ∀ {N V A B C D gc₁ gc₂ ℓ₁ ℓ₂} {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ₙ : CExpr l ℓ₁ ⇒ l ℓ₂}
               {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC PC′}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → (stampₑ PC vc ℓ₂) ⟪ d̅ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      ---------------------------------------------------------------------------- AppCast
    → app (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D ℓ₂ ∣ μ ∣ PC —→
         `let (V ⟨ c ⟩) A (prot PC′ r ℓ₂ (N ⟨ d ⟩) D) ∣ μ

  app!-cast : ∀ {N V A B C D gc ℓ g} {d̅ : CExpr ⋆ ⇒ gc} {c̅ₙ : CExpr l ℓ ⇒ g}
                {c : Cast C ⇒ A} {d : Cast B ⇒ D} {μ PC PC′} {gc′}
    → (v  : Value V)
    → (vc : LVal PC)
    → (𝓋  : CVal c̅ₙ)
    → ⊢ PC ⇐ gc′
    → let ℓ′ = ∥ c̅ₙ ∥ₗ 𝓋 in
       (stampₑ PC vc ℓ′) ⟪ coerce (gc ⋎̃ l ℓ′) ⇒⋆ ⟫ ⟪ d̅ ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      ---------------------------------------------------------------------------- App!Cast
    → app! (ƛ N ⟨ cast (fun d̅ c d) c̅ₙ ⟩) V C D g ∣ μ ∣ PC —→
         `let (V ⟨ c ⟩) A (prot PC′ r ℓ′ (N ⟨ d ⟩) D) ∣ μ

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

  ref?-blame : ∀ {ℓ V n p μ PC}
    → (v : Value V)
    → a⟦ ℓ ⟧ n FreshIn μ
    → PC ⟪ coerceₗ {⋆} {l ℓ} ≾-⋆l p ⟫ —↠ₑ bl p
      -------------------------------------------------------------------- Ref?Blame
    → ref?⟦ ℓ ⟧ V p ∣ μ ∣ PC —→ blame p ∣ μ

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

  -- assign-static : ∀ {L M μ pc}
  --     ------------------------------------------------------- AssignStatic
  --   → assign L M ∣ μ ∣ pc —→ assign✓ L M ∣ μ

  -- β-assign : ∀ {V μ pc n ℓ ℓ̂}
  --   → (v : Value V)
  --     ---------------------------------------------------------------------------------------------- Assign
  --   → assign✓ (addr (a⟦ ℓ̂ ⟧ n) of ℓ) V ∣ μ ∣ pc —→ $ tt of low ∣ cons-μ (a⟦ ℓ̂ ⟧ n) V v μ

  -- cast : ∀ {A B V M μ pc} {c : Cast A ⇒ B}
  --   → Value V → Active c
  --   → ApplyCast V , c ↝ M
  --     ----------------------------------- Cast
  --   → V ⟨ c ⟩ ∣ μ ∣ pc —→ M ∣ μ

  -- β-if⋆-true : ∀ {M N μ pc A g ℓ} {p} {c~ : (` Bool of g) ~ (` Bool of ⋆)}
  --     --------------------------------------------------------------------------------- IfCastTrue
  --   → let c = cast _ _ p c~ in
  --      if⋆ ($ true of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ (prot ⋆ ℓ M) ⟨ branch/c A c ⟩ ∣ μ

  -- β-if⋆-false : ∀ {M N μ pc A g ℓ} {p} {c~ : (` Bool of g) ~ (` Bool of ⋆)}
  --     --------------------------------------------------------------------------------- IfCastFalse
  --   → let c = cast _ _ p c~ in
  --      if⋆ ($ false of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ (prot ⋆ ℓ N) ⟨ branch/c A c ⟩ ∣ μ

  -- app?-ok : ∀ {V M μ pc A B C D ℓ ℓᶜ} {p q}
  --             {c~ : ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ ~ ⟦ ⋆ ⟧ C ⇒ D of ⋆}
  --   → Value V
  --   → nsu pc ℓ ℓᶜ
  --     ----------------------------------------------------------------------------- App?Success
  --   → let c = cast (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ) (⟦ ⋆ ⟧ C ⇒ D of ⋆) p c~ in
  --      app? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ (app✓ V (M ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩ ∣ μ

  -- app?-fail : ∀ {V M μ pc A B C D ℓ ℓᶜ} {p q}
  --               {c~ : ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ ~ ⟦ ⋆ ⟧ C ⇒ D of ⋆}
  --   → Value V
  --   → ¬ nsu pc ℓ ℓᶜ
  --     ----------------------------------------------------------------------------- App?Fail
  --   → let c = cast (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ) (⟦ ⋆ ⟧ C ⇒ D of ⋆) p c~ in
  --      app? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ blame nsu-error q ∣ μ

  -- fun-cast : ∀ {V W μ pc A B C D ℓᶜ₁ ℓᶜ₂ ℓ₁ ℓ₂} {p}
  --              {c~ : (⟦ l ℓᶜ₁ ⟧ A ⇒ B of l ℓ₁) ~ (⟦ l ℓᶜ₂ ⟧ C ⇒ D of l ℓ₂)}
  --   → Value V → Value W
  --     ----------------------------------------------------------------------------- FunCast
  --   → let c = cast (⟦ l ℓᶜ₁ ⟧ A ⇒ B of l ℓ₁) (⟦ l ℓᶜ₂ ⟧ C ⇒ D of l ℓ₂) p c~ in
  --      app✓ (V ⟨ c ⟩) W ∣ μ ∣ pc —→ (app✓ V (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩ ∣ μ

  -- deref-cast : ∀ {V μ pc S T ℓ ℓ̂ g ĝ} {p}
  --                {c~ : (Ref (S of l ℓ̂) of l ℓ) ~ (Ref (T of ĝ) of g)}
  --   → Value V
  --     --------------------------------------------------------------------- DerefCast
  --   → let c = cast (Ref (S of l ℓ̂) of l ℓ) (Ref (T of ĝ) of g) p c~ in
  --      ! (V ⟨ c ⟩) ∣ μ ∣ pc —→ ! V ⟨ out/c c ⟩ ∣ μ

  -- assign?-ok : ∀ {V M μ pc S T ℓ ℓ̂} {p q} {c~ : Ref (S of l ℓ̂) of l ℓ ~ Ref (T of ⋆) of ⋆}
  --   → Value V
  --   → nsu pc ℓ ℓ̂
  --     ----------------------------------------------------------------------------- Assign?Success
  --   → let c = cast (Ref (S of l ℓ̂) of l ℓ) (Ref (T of ⋆) of ⋆) p c~ in
  --      assign? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ assign✓ V (M ⟨ in/c c ⟩) ∣ μ

  -- assign?-fail : ∀ {V M μ pc S T ℓ ℓ̂} {p q} {c~ : Ref (S of l ℓ̂) of l ℓ ~ Ref (T of ⋆) of ⋆}
  --   → Value V
  --   → ¬ nsu pc ℓ ℓ̂
  --     ----------------------------------------------------------------------------- Assign?Fail
  --   → let c = cast (Ref (S of l ℓ̂) of l ℓ) (Ref (T of ⋆) of ⋆) p c~ in
  --      assign? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ blame nsu-error q ∣ μ
  --      {- blame the projection assign? -}

  -- assign-cast : ∀ {V W μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
  --   → Value V → Value W
  --   → (i : Inert c)
  --     ------------------------------------------------------------------------ AssignCast
  --   → assign✓ (V ⟨ c ⟩) W ∣ μ ∣ pc —→ assign✓ V (W ⟨ in/c c ⟩) ∣ μ
