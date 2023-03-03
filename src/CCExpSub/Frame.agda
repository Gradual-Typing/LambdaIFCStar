{- Evaluation contexts -}

module CCExpSub.Frame where

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Function using (case_of_)

open import Common.Types
open import Memory.HeapContext
open import CCExpSub.Statics


data Frame : HeapContext → (gcₒ gcᵢ : Label) → StaticLabel → (A B : Type) →  Set where

  □·_ : ∀ {Σ gc pc A B g} (M : Term)
    → [] ; Σ ; gc ; pc ⊢ M ⦂ A
    → Frame Σ gc gc pc (⟦ gc ⋎̃ g ⟧ A ⇒ B of g) (stamp B g)

  _·□ : ∀ {Σ gc pc A B g} (V : Term)
    → [] ; Σ ; gc ; pc ⊢ V ⦂ ⟦ gc ⋎̃ g ⟧ A ⇒ B of g
    → Value V
    → Frame Σ gc gc pc A (stamp B g)

  ref✓⟦_⟧□ : ∀ {Σ gc pc T} ℓ
    → pc ≼ ℓ
    → Frame Σ gc gc pc (T of l ℓ) (Ref (T of l ℓ) of l low)

  !□ : ∀ {Σ gc pc A g}
    → Frame Σ gc gc pc (Ref A of g) (stamp A g)

  □:=?_ : ∀ {Σ gc pc T g} (M : Term)
    → (∀ {pc} → [] ; Σ ; gc ; pc ⊢ M ⦂ T of g)
    → Frame Σ gc gc pc (Ref (T of g) of g) (` Unit of l low)

  □:=✓_ : ∀ {Σ gc pc T ℓ} (M : Term)
    → [] ; Σ ; gc ; pc ⊢ M ⦂ T of l ℓ
    → pc ≼ ℓ
    → Frame Σ gc gc pc (Ref (T of l ℓ) of l ℓ) (` Unit of l low)

  _:=✓□ : ∀ {Σ gc pc T ℓ} (V : Term)
    → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref (T of l ℓ) of l ℓ
    → Value V
    → pc ≼ ℓ
    → Frame Σ gc gc pc (T of l ℓ) (` Unit of l low)

  let□_ : ∀ {Σ gc pc A B} (N : Term)
    → (∀ {pc} → A ∷ [] ; Σ ; gc ; pc ⊢ N ⦂ B)
    → Frame Σ gc gc pc A B

  if□ : ∀ {Σ gc pc g} (A : Type) (M N : Term)
    → (∀ {pc} → [] ; Σ ; gc ⋎̃ g ; pc ⊢ M ⦂ A)
    → (∀ {pc} → [] ; Σ ; gc ⋎̃ g ; pc ⊢ N ⦂ A)
    → Frame Σ gc gc pc (` Bool of g) (stamp A g)

  □⟨_⟩ : ∀ {Σ gc pc A B}
    → Cast A ⇒ B
    → Frame Σ gc gc pc A B

  □↟⟨_⟩ : ∀ {Σ gc pc A B}
    → A ↟ B
    → Frame Σ gc gc pc A B

  cast-pc_□ : ∀ {Σ gc pc A} (g : Label)
    → l pc ~ₗ g
    → Frame Σ gc g pc A A


plug : ∀ {Σ gcₒ gcᵢ pc A B} → Term → Frame Σ gcₒ gcᵢ pc A B → Term
plug L ((□· M) ⊢M)           = L · M
plug M ((V ·□) ⊢V v)         = V · M
plug M ((ref✓⟦ ℓ ⟧□) _)     = ref✓⟦ ℓ ⟧ M
plug M !□                    = ! M
plug L ((□:=? M) ⊢M)         = L :=? M
plug L ((□:=✓ M) ⊢M _)      = L :=✓ M
plug M ((V :=✓□) ⊢V v _)    = V :=✓ M
plug M ((let□ N) ⊢N)         = `let M N
plug L (if□ A M N ⊢M ⊢N)     = if L A M N
plug M □⟨ c ⟩                = M ⟨ c ⟩
plug M □↟⟨ s ⟩              = M ↟⟨ s ⟩
plug M ((cast-pc g □) pc~g)  = cast-pc g M

plug-wt : ∀ {Σ gcₒ gcᵢ pc A B} (M : Term)
  → ([] ; Σ ; gcᵢ ; pc ⊢ M ⦂ A)
  → (F : Frame Σ gcₒ gcᵢ pc A B)
  → [] ; Σ ; gcₒ ; pc ⊢ plug M F ⦂ B
plug-wt L ⊢L ((□· M) ⊢M)           = ⊢app ⊢L ⊢M
plug-wt M ⊢M ((V ·□) ⊢V v)         = ⊢app ⊢V ⊢M
plug-wt M ⊢M ((ref✓⟦ ℓ ⟧□) pc≼ℓ)  = ⊢ref✓ ⊢M pc≼ℓ
plug-wt M ⊢M !□                    = ⊢deref ⊢M
plug-wt L ⊢L ((□:=? M) ⊢M)         = ⊢assign? ⊢L ⊢M
plug-wt L ⊢L ((□:=✓ M) ⊢M pc≼ℓ)   = ⊢assign✓ ⊢L ⊢M pc≼ℓ
plug-wt M ⊢M ((V :=✓□) ⊢V v pc≼ℓ) = ⊢assign✓ ⊢V ⊢M pc≼ℓ
plug-wt M ⊢M ((let□ N) ⊢N)         = ⊢let ⊢M ⊢N
plug-wt L ⊢L (if□ A M N ⊢M ⊢N)     = ⊢if ⊢L ⊢M ⊢N
plug-wt M ⊢M □⟨ c ⟩                = ⊢cast ⊢M
plug-wt M ⊢M □↟⟨ s ⟩              = ⊢sub ⊢M
plug-wt M ⊢M ((cast-pc g □) pc~g)  = ⊢cast-pc ⊢M pc~g
