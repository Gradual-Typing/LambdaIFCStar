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
open import Common.Types
open import CC2.CCStatics
open import Memory.Heap Term Value

open import CC2.ApplyCast        public
open import CC2.Frame            public


nsu : StaticLabel → StaticLabel → StaticLabel → Set
nsu ℓ₁ ℓ₂ ℓ = ℓ₁ ≼ ℓ × ℓ₂ ≼ ℓ

nsu? : ∀ ℓ₁ ℓ₂ ℓ → Dec (nsu ℓ₁ ℓ₂ ℓ)
nsu? high high high = yes ⟨ h≼h , h≼h ⟩
nsu? high high low  = no λ { ⟨ _ , () ⟩ }
nsu? high low high  = yes ⟨ h≼h , l≼h ⟩
nsu? high low low   = no λ { ⟨ () , _ ⟩ }
nsu? low high high  = yes ⟨ l≼h , h≼h ⟩
nsu? low high low   = no λ { ⟨ _ , () ⟩ }
nsu? low low high   = yes ⟨ l≼h , l≼h ⟩
nsu? low low low    = yes ⟨ l≼l , l≼l ⟩


infix 2 _∣_∣_—→_∣_

data _∣_∣_—→_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ pc}
    → M        ∣ μ ∣ pc —→ M′        ∣ μ′
      ---------------------------------------------- ξ
    → plug M F ∣ μ ∣ pc —→ plug M′ F ∣ μ′

  ξ-err : ∀ {F μ pc e p}
      ---------------------------------------------- ξ-error
    → plug (blame e p) F ∣ μ ∣ pc —→ blame e p ∣ μ

  prot-val : ∀ {V μ pc ℓ}
    → (v : Value V)
      --------------------------------------------------- ProtectVal
    → prot ℓ V ∣ μ ∣ pc —→ stamp-val V v ℓ ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ pc ℓ}
    → M        ∣ μ ∣ pc ⋎ ℓ —→ M′        ∣ μ′
      --------------------------------------------------- ProtectContext
    → prot ℓ M ∣ μ ∣ pc     —→ prot ℓ M′ ∣ μ′

  prot-err : ∀ {μ pc ℓ e p}
      --------------------------------------------------- ProtectContext
    → prot ℓ (blame e p) ∣ μ ∣ pc —→ blame e p ∣ μ

  app-static : ∀ {L M μ pc}
      ------------------------------------- AppStatic
    → app L M ∣ μ ∣ pc —→ app✓ L M ∣ μ

  β : ∀ {V N μ pc pc′ A ℓ}
    → Value V
      ------------------------------------------------------------------- β
    → app✓ (ƛ⟦ pc′ ⟧ A ˙ N of ℓ) V ∣ μ ∣ pc —→ prot ℓ (N [ V ]) ∣ μ

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
    → ref⟦ ℓ ⟧ M ∣ μ ∣ pc —→ ref✓⟦ ℓ ⟧ M ∣ μ

  ref?-ok : ∀ {M μ pc ℓ p}
    → pc ≼ ℓ
      ------------------------------------------------- Ref?Success
    → ref?⟦ ℓ ⟧ M p ∣ μ ∣ pc —→ ref✓⟦ ℓ ⟧ M ∣ μ

  ref?-fail : ∀ {M μ pc ℓ p}
    → ¬ pc ≼ ℓ
      ------------------------------------------------- Ref?Fail
    → ref?⟦ ℓ ⟧ M p ∣ μ ∣ pc —→ blame nsu-error p ∣ μ

  ref : ∀ {V μ pc n ℓ}
    → (v : Value V)
    → a⟦ ℓ ⟧ n FreshIn μ  {- address is fresh -}
      -------------------------------------------------------------------------------- Ref
    → ref✓⟦ ℓ ⟧ V ∣ μ ∣ pc —→ addr (a⟦ ℓ ⟧ n) of low ∣ cons-μ (a⟦ ℓ ⟧ n) V v μ

  deref : ∀ {V μ pc v n ℓ ℓ̂}
    → lookup-μ μ (a⟦ ℓ̂ ⟧ n) ≡ just (V & v)
      --------------------------------------------------------------------- Deref
    → ! (addr (a⟦ ℓ̂ ⟧ n) of ℓ) ∣ μ ∣ pc —→ prot (ℓ̂ ⋎ ℓ) V ∣ μ

  assign-static : ∀ {L M μ pc}
      ------------------------------------------------------- AssignStatic
    → assign L M ∣ μ ∣ pc —→ assign✓ L M ∣ μ

  β-assign : ∀ {V μ pc n ℓ ℓ̂}
    → (v : Value V)
      ---------------------------------------------------------------------------------------------- Assign
    → assign✓ (addr (a⟦ ℓ̂ ⟧ n) of ℓ) V ∣ μ ∣ pc —→ $ tt of low ∣ cons-μ (a⟦ ℓ̂ ⟧ n) V v μ

  cast : ∀ {A B V M μ pc} {c : Cast A ⇒ B}
    → Value V → Active c
    → ApplyCast V , c ↝ M
      ----------------------------------- Cast
    → V ⟨ c ⟩ ∣ μ ∣ pc —→ M ∣ μ

  if-cast-true : ∀ {M N μ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastTrue
    → if ($ true of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ prot ℓ (cast-pc ⋆ M) ⟨ branch/c A c ⟩ ∣ μ

  if-cast-false : ∀ {M N μ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastFalse
    → if ($ false of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ prot ℓ (cast-pc ⋆ N) ⟨ branch/c A c ⟩ ∣ μ

  app?-ok : ∀ {V M μ pc A B C D ℓ ℓᶜ} {p q} {c~ : ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ ~ ⟦ ⋆ ⟧ C ⇒ D of ⋆}
    → Value V
    → nsu pc ℓ ℓᶜ
      ----------------------------------------------------------------------------- App?Success
    → let c = cast (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ) (⟦ ⋆ ⟧ C ⇒ D of ⋆) p c~ in
       app? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ (app✓ V (M ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩ ∣ μ

  app?-fail : ∀ {V M μ pc A B C D ℓ ℓᶜ} {p q} {c~ : ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ ~ ⟦ ⋆ ⟧ C ⇒ D of ⋆}
    → Value V
    → ¬ nsu pc ℓ ℓᶜ
      ----------------------------------------------------------------------------- App?Fail
    → let c = cast (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ) (⟦ ⋆ ⟧ C ⇒ D of ⋆) p c~ in
       app? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ blame nsu-error q ∣ μ

  fun-cast : ∀ {V W μ pc A B C D gc₁ gc₂ g₁ g₂} {c : Cast (⟦ gc₁ ⟧ A ⇒ B of g₁) ⇒ (⟦ gc₂ ⟧ C ⇒ D of g₂)}
    → Value V → Value W
    → (i : Inert c)
      ----------------------------------------------------------------------------- FunCast
    → app✓ (V ⟨ c ⟩) W ∣ μ ∣ pc —→ (app✓ V (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩ ∣ μ

  deref-cast : ∀ {V μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → Inert c
      ------------------------------------------------------ DerefCast
    → ! (V ⟨ c ⟩) ∣ μ ∣ pc —→ ! V ⟨ out/c c ⟩ ∣ μ

  assign?-ok : ∀ {V M μ pc S T ℓ ℓ̂} {p q} {c~ : Ref (S of l ℓ̂) of l ℓ ~ Ref (T of ⋆) of ⋆}
    → Value V
    → nsu pc ℓ ℓ̂
      ----------------------------------------------------------------------------- Assign?Success
    → let c = cast (Ref (S of l ℓ̂) of l ℓ) (Ref (T of ⋆) of ⋆) p c~ in
       assign? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ assign✓ V (M ⟨ in/c c ⟩) ∣ μ

  assign?-fail : ∀ {V M μ pc S T ℓ ℓ̂} {p q} {c~ : Ref (S of l ℓ̂) of l ℓ ~ Ref (T of ⋆) of ⋆}
    → Value V
    → ¬ nsu pc ℓ ℓ̂
      ----------------------------------------------------------------------------- Assign?Fail
    → let c = cast (Ref (S of l ℓ̂) of l ℓ) (Ref (T of ⋆) of ⋆) p c~ in
       assign? (V ⟨ c ⟩) M q ∣ μ ∣ pc —→ blame nsu-error q ∣ μ
       {- blame the projection assign? -}

  assign-cast : ∀ {V W μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V → Value W
    → (i : Inert c)
      ------------------------------------------------------------------------ AssignCast
    → assign✓ (V ⟨ c ⟩) W ∣ μ ∣ pc —→ assign✓ V (W ⟨ in/c c ⟩) ∣ μ

  β-cast-pc : ∀ {V μ pc g}
    → Value V
      ------------------------------------- CastPC
    → cast-pc g V ∣ μ ∣ pc —→ V ∣ μ
