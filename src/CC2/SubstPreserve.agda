module CC2.SubstPreserve where

open import Data.Nat
open import Data.List hiding ([_])
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)

open import Syntax

open import Common.Types
open import Memory.HeapContext using (HeapContext)
open import CC2.Statics


_⦂_⇒_ : Rename → List Type → List Type → Set
ρ ⦂ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A

ext-pres : ∀ {Γ Δ ρ A}
  → ρ ⦂ Γ ⇒ Δ
  → ext ρ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-pres ⊢ρ {0} eq = eq
ext-pres ⊢ρ {suc x} Γ∋x = ⊢ρ Γ∋x

rename-pres : ∀ {Γ Δ : Context} {Σ gc ℓv A M ρ}
  → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ A
  → ρ ⦂ Γ ⇒ Δ
    -----------------------------
  → Δ ; Σ ; gc ; ℓv ⊢ rename ρ M ⇐ A
rename-pres ⊢const ⊢ρ = ⊢const
rename-pres (⊢addr eq) ⊢ρ = ⊢addr eq
rename-pres (⊢var Γ∋x) ⊢ρ = ⊢var (⊢ρ Γ∋x)
rename-pres {Γ} {Δ} (⊢lam ⊢N) ⊢ρ =
  ⊢lam (rename-pres ⊢N (λ {x} {A} → ext-pres {Γ} {Δ} ⊢ρ {x} {A}))
rename-pres (⊢app  ⊢L ⊢M eq) ⊢ρ = ⊢app  (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) eq
rename-pres (⊢app! ⊢L ⊢M eq) ⊢ρ = ⊢app! (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) eq
rename-pres (⊢if ⊢L ⊢M ⊢N eq) ⊢ρ =
  ⊢if (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) (rename-pres ⊢N ⊢ρ) eq
rename-pres (⊢if! ⊢L ⊢M ⊢N eq) ⊢ρ =
  ⊢if! (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) (rename-pres ⊢N ⊢ρ) eq
rename-pres {Γ} {Δ} (⊢let ⊢M ⊢N) ⊢ρ =
  ⊢let (rename-pres ⊢M ⊢ρ) (rename-pres ⊢N (λ {x} {A} → ext-pres {Γ} {Δ} ⊢ρ {x} {A}))
rename-pres (⊢ref ⊢M x) ⊢ρ = ⊢ref (rename-pres ⊢M ⊢ρ) x
rename-pres (⊢ref? ⊢M) ⊢ρ = ⊢ref? (rename-pres ⊢M ⊢ρ)
rename-pres (⊢deref ⊢M eq) ⊢ρ = ⊢deref (rename-pres ⊢M ⊢ρ) eq
rename-pres (⊢deref! ⊢M eq) ⊢ρ = ⊢deref! (rename-pres ⊢M ⊢ρ) eq
rename-pres (⊢assign ⊢L ⊢M x y) ⊢ρ = ⊢assign (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) x y
rename-pres (⊢assign? ⊢L ⊢M) ⊢ρ = ⊢assign? (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ)
rename-pres (⊢prot ⊢M ⊢PC x eq) ⊢ρ = ⊢prot (rename-pres ⊢M ⊢ρ) ⊢PC x eq
rename-pres ⊢prot-blame-pc ⊢ρ = ⊢prot-blame-pc
rename-pres (⊢cast ⊢M) ⊢ρ = ⊢cast (rename-pres ⊢M ⊢ρ)
rename-pres ⊢blame ⊢ρ = ⊢blame

rename-↑1-pres : ∀ {Γ Σ gc ℓv M A B}
  → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ B
    ------------------------------------------------------------
  → (A ∷ Γ) ; Σ ; gc ; ℓv ⊢ rename (Syntax.↑ 1) M ⇐ B
rename-↑1-pres ⊢M = rename-pres ⊢M (λ {x} {A} Γ∋x → Γ∋x)

_⊢_⦂_⇒_ : HeapContext → Subst → List Type → List Type → Set
Σ ⊢ σ ⦂ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → (∀ {gc ℓv} → Δ ; Σ ; gc ; ℓv ⊢ σ x ⇐ A)

exts-pres : ∀ {Σ Γ Δ σ A}
  → Σ ⊢ σ ⦂ Γ ⇒ Δ
  → Σ ⊢ ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
exts-pres ⊢σ {0} eq = (⊢var eq)
exts-pres ⊢σ {suc x} Γ∋x = rename-↑1-pres (⊢σ Γ∋x)

subst-pres : ∀ {Σ} {Γ Δ : Context} {gc ℓv A M σ}
  → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ A
  → Σ ⊢ σ ⦂ Γ ⇒ Δ
    -----------------------------------
  → Δ ; Σ ; gc ; ℓv ⊢ ⦅ σ ⦆ M ⇐ A
subst-pres ⊢const ⊢σ = ⊢const
subst-pres (⊢addr eq) ⊢σ = ⊢addr eq
subst-pres (⊢var Γ∋x) ⊢σ = ⊢σ Γ∋x
subst-pres {Γ} {Δ} (⊢lam ⊢N) ⊢σ =
  ⊢lam (subst-pres ⊢N (λ {x} {A} → exts-pres {Γ} {Δ} ⊢σ {x} {A}))
subst-pres (⊢app  ⊢L ⊢M eq) ⊢σ = ⊢app  (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ) eq
subst-pres (⊢app! ⊢L ⊢M eq) ⊢σ = ⊢app! (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ) eq
subst-pres (⊢if ⊢L ⊢M ⊢N eq) ⊢σ =
  ⊢if (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ) (subst-pres ⊢N ⊢σ) eq
subst-pres (⊢if! ⊢L ⊢M ⊢N eq) ⊢σ =
  ⊢if! (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ) (subst-pres ⊢N ⊢σ) eq
subst-pres {Γ} {Δ} (⊢let ⊢M ⊢N) ⊢σ =
  ⊢let (subst-pres ⊢M ⊢σ) (subst-pres ⊢N (λ {x} {A} → exts-pres {Γ} {Δ} ⊢σ {x} {A}))
subst-pres (⊢ref ⊢M x) ⊢σ = ⊢ref (subst-pres ⊢M ⊢σ) x
subst-pres (⊢ref? ⊢M) ⊢σ = ⊢ref? (subst-pres ⊢M ⊢σ)
subst-pres (⊢deref ⊢M eq) ⊢σ = ⊢deref (subst-pres ⊢M ⊢σ) eq
subst-pres (⊢deref! ⊢M eq) ⊢σ = ⊢deref! (subst-pres ⊢M ⊢σ) eq
subst-pres (⊢assign ⊢L ⊢M x y) ⊢σ = ⊢assign (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ) x y
subst-pres (⊢assign? ⊢L ⊢M) ⊢σ = ⊢assign? (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ)
subst-pres (⊢prot ⊢M ⊢PC x eq) ⊢σ = ⊢prot (subst-pres ⊢M ⊢σ) ⊢PC x eq
subst-pres ⊢prot-blame-pc ⊢σ = ⊢prot-blame-pc
subst-pres (⊢cast ⊢M) ⊢σ = ⊢cast (subst-pres ⊢M ⊢σ)
subst-pres ⊢blame ⊢σ = ⊢blame

substitution-pres : ∀ {Γ Σ gc pc N V A B}
  → (A ∷ Γ) ; Σ ; gc ; pc ⊢ N ⇐ B
  → (∀ {gc′ ℓv′} → Γ ; Σ ; gc′ ; ℓv′ ⊢ V ⇐ A)
    ------------------------------------------------
  → Γ ; Σ ; gc ; pc ⊢ N [ V ] ⇐ B
substitution-pres ⊢N ⊢V =
  subst-pres ⊢N (λ { {0} refl → ⊢V ; {suc x} ∋x → ⊢var ∋x })
