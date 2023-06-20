module CC2.Reduction where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Utils
open import CC2.Statics
open import CC2.Frame public
open import Memory.Heap Term Value


infix 2 _∣_∣_—→_∣_

data _∣_∣_—→_∣_ : Term → Heap → ∃[ PC ] LVal PC → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ PC v}
    →        M ∣ μ ∣ ⟨ PC , v ⟩ —→ M′        ∣ μ′
      -------------------------------------------------- ξ
    → plug M F ∣ μ ∣ ⟨ PC , v ⟩ —→ plug M′ F ∣ μ′

  ξ-err : ∀ {F μ PC v p}
      ------------------------------------------------------ ξ-blame
    → plug (blame p) F ∣ μ ∣ ⟨ PC , v ⟩ —→ blame p ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ PC PC′ A ℓ} {v v′}
    →                         M ∣ μ ∣ ⟨ PC  , v  ⟩ —→ M′ ∣ μ′
      ---------------------------------------------------------------------------- ProtectContext
    → prot PC (success v) ℓ M A ∣ μ ∣ ⟨ PC′ , v′ ⟩ —→ prot PC (success v) ℓ M′ A ∣ μ′

  prot-val : ∀ {Σ gc ℓv V μ PC PC′ A ℓ} {vc vc′}
    → (v  : Value V)
    → (⊢V : [] ; Σ ; gc ; ℓv ⊢ V ⇐ A)
      ------------------------------------------------------------------------ ProtectValue
    → prot PC (success vc) ℓ V A ∣ μ ∣ ⟨ PC′ , vc′ ⟩ —→ stamp-val V v ⊢V ℓ ∣ μ

  prot-err : ∀ {μ PC PC′ A ℓ p} {v v′}
      ------------------------------------------------------------------------ ProtectBlame
    → prot PC (success v) ℓ (blame p) A ∣ μ ∣ ⟨ PC′ , v′ ⟩ —→ blame p ∣ μ

  prot-err-pc : ∀ {M μ PC A ℓ p} {v}
      ------------------------------------------------------------------ ProtectBlamePC
    → prot (bl p) fail ℓ M A ∣ μ ∣ ⟨ PC , v ⟩ —→ blame p ∣ μ

  cast : ∀ {Vᵣ S T g₁ g₂} {cᵣ : Castᵣ S ⇒ T} {c̅ c̅ₙ : CExpr g₁ ⇒ g₂} {μ PC} {v}
    → RawValue Vᵣ
    → c̅ —↠ c̅ₙ
    → CVal c̅ₙ
      ---------------------------------------------------------------- Cast
    → Vᵣ ⟨ cast cᵣ c̅ ⟩ ∣ μ ∣ ⟨ PC , v ⟩ —→ Vᵣ ⟨ cast cᵣ c̅ₙ ⟩ ∣ μ

  cast-blame : ∀ {Vᵣ S T g₁ g₂} {cᵣ : Castᵣ S ⇒ T} {c̅ c̅ₙ : CExpr g₁ ⇒ g₂} {μ PC p} {v}
    → RawValue Vᵣ
    → c̅ —↠ ⊥ g₁ g₂ p
      ----------------------------------------------------------- CastBlame
    → Vᵣ ⟨ cast cᵣ c̅ ⟩ ∣ μ ∣ ⟨ PC , v ⟩ —→ blame p ∣ μ

  cast-id : ∀ {ι g} {k : rep ι} {μ PC} {v}
      ----------------------------------------------------------- CastId
    → $ k ⟨ cast (id ι) (id g) ⟩ ∣ μ ∣ ⟨ PC , v ⟩ —→ $ k ∣ μ

  cast-comp : ∀ {Vᵣ A B C} {cᵢ : Cast A ⇒ B} {d : Cast B ⇒ C} {μ PC} {v}
    → RawValue Vᵣ
    → Irreducible cᵢ
      ---------------------------------------------------------- CastComposition
    → Vᵣ ⟨ cᵢ ⟩ ⟨ d ⟩ ∣ μ ∣ ⟨ PC , v ⟩ —→ Vᵣ ⟨ cᵢ ⨟ d ⟩ ∣ μ

  β : ∀ {N V A B ℓ μ PC} {vc}
    → (v : Value V)
      ------------------------------------------------------------------------------ App
    → app (ƛ N) V A B ℓ ∣ μ ∣ ⟨ PC , vc ⟩ —→
         prot (stampₑ PC vc ℓ) (success (stampₑ-LVal vc)) ℓ (N [ V ]) B ∣ μ

  β-app! : ∀ {N V A B ℓ μ PC PC′} {gc vc}
    → (v : Value V)
    → ⊢ PC ⇐ gc
    → (stampₑ PC vc ℓ) ⟪ coerce-to⋆ (gc ⋎̃ l ℓ) ⟫ —↠ₑ PC′
    → (r : LResult PC′)
      ------------------------------------------------------------------------------ App!
    → app! (ƛ N) V A B (l ℓ) ∣ μ ∣ ⟨ PC , vc ⟩ —→ prot PC′ r ℓ (N [ V ]) B ∣ μ

  -- β-if-true : ∀ {M N μ pc A ℓ}
  --     ----------------------------------------------------------------------- IfTrue
  --   → if ($ true of ℓ) A M N ∣ μ ∣ pc —→ prot (l pc) ℓ M ∣ μ

  -- β-if-false : ∀ {M N μ pc A ℓ}
  --     ----------------------------------------------------------------------- IfFalse
  --   → if ($ false of ℓ) A M N ∣ μ ∣ pc —→ prot (l pc) ℓ N ∣ μ

  -- β-let : ∀ {V N μ pc}
  --   → Value V
  --     -------------------------------------- Let
  --   → `let V N ∣ μ ∣ pc —→ N [ V ] ∣ μ

  -- ref-static : ∀ {M μ pc ℓ}
  --     ------------------------------------------------- RefStatic
  --   → ref⟦ ℓ ⟧ M ∣ μ ∣ pc —→ ref✓⟦ ℓ ⟧ M ∣ μ

  -- ref?-ok : ∀ {M μ pc ℓ p}
  --   → pc ≼ ℓ
  --     ------------------------------------------------- Ref?Success
  --   → ref?⟦ ℓ ⟧ M p ∣ μ ∣ pc —→ ref✓⟦ ℓ ⟧ M ∣ μ

  -- ref?-fail : ∀ {M μ pc ℓ p}
  --   → ¬ pc ≼ ℓ
  --     ------------------------------------------------- Ref?Fail
  --   → ref?⟦ ℓ ⟧ M p ∣ μ ∣ pc —→ blame nsu-error p ∣ μ

  -- ref : ∀ {V μ pc n ℓ}
  --   → (v : Value V)
  --   → a⟦ ℓ ⟧ n FreshIn μ  {- address is fresh -}
  --     -------------------------------------------------------------------------------- Ref
  --   → ref✓⟦ ℓ ⟧ V ∣ μ ∣ pc —→ addr (a⟦ ℓ ⟧ n) of low ∣ cons-μ (a⟦ ℓ ⟧ n) V v μ

  -- deref : ∀ {V μ pc v n ℓ ℓ̂}
  --   → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
  --     --------------------------------------------------------------------- Deref
  --   → ! (addr (a⟦ ℓ̂ ⟧ n) of ℓ) ∣ μ ∣ pc —→ prot (l pc) (ℓ̂ ⋎ ℓ) V ∣ μ

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
