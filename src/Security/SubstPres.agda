open import Common.Types

module Security.SubstPres where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax hiding (_⨟_)
open import Common.Utils

open import Common.Coercions
open import Memory.Addr
open import CC2.Statics
  renaming (Term to CCTerm; `_ to var; $_ to const; ƛ to lam; addr to adrs; if to `if;
            ref⟦_⟧ to refer; ref?⟦_⟧ to refer?; prot to protect; ! to deref; !⋆ to deref⋆)
open import Dyn.Syntax
open import Security.SimRel
open import CC2.SubstPreserve using (_⊢_⦂_⇒_)


infix 4 _≋_

data _≋_ : Type → Type → Set where

  sim-base : ∀ {ι g} → ` ι of g ≋ ` ι of g

  sim-ref : ∀ {A B g}
    → A ≋ B
    → Ref A of g ≋ Ref B of g

  sim-fun : ∀ {A₁ A₂ B₁ B₂ g₁ g₂ g}
    → A₁ ≋ A₂
    → B₁ ≋ B₂
    → ⟦ g₁ ⟧ A₁ ⇒ B₁ of g ≋ ⟦ g₂ ⟧ A₂ ⇒ B₂ of g

≋-refl : ∀ {A} → A ≋ A
≋-refl {` x of x₁} = sim-base
≋-refl {(Ref A) of g} = sim-ref ≋-refl
≋-refl {⟦ _ ⟧ A ⇒ B of g} = sim-fun ≋-refl ≋-refl

_≤ˢ_⇐_ : ∀ (σ′ : Dyn.Syntax.Subst) (σ : CC2.Statics.Subst) → (Γ : Context) → Set
σ′ ≤ˢ σ ⇐ Γ =
  (∀ x {A B}
    → Γ ∋ x ⦂ A
    → A ≋ B
    → σ′ x ≤ σ x ⇐ B)

rename-pres-≤ : ∀ {A} {M M′} {ρ : Rename}
  → M′ ≤ M ⇐ A
    -----------------------------------------------------------------------------
  → Dyn.Syntax.rename ρ M′ ≤ CC2.Statics.rename ρ M ⇐ A
rename-pres-≤ ≤-var = ≤-var
rename-pres-≤ (≤-const x) = ≤-const x
rename-pres-≤ (≤-wrapped-const x y z) = ≤-wrapped-const x y z
rename-pres-≤ {ρ = ρ} (≤-lam N′≤N x) = ≤-lam (rename-pres-≤ {ρ = ext ρ} N′≤N) x
rename-pres-≤ {ρ = ρ} (≤-wrapped-lam N′≤N x y) = ≤-wrapped-lam (rename-pres-≤ {ρ = ext ρ} N′≤N) x y
rename-pres-≤ (≤-addr x) = ≤-addr x
rename-pres-≤ (≤-wrapped-addr x y) = ≤-wrapped-addr x y
rename-pres-≤ (≤-app M′≤M N′≤N) = ≤-app (rename-pres-≤ M′≤M) (rename-pres-≤ N′≤N)
rename-pres-≤ (≤-app⋆ M′≤M N′≤N) = ≤-app⋆ (rename-pres-≤ M′≤M) (rename-pres-≤ N′≤N)
rename-pres-≤ (≤-if L′≤L M′≤M N′≤N) = ≤-if (rename-pres-≤ L′≤L) (rename-pres-≤ M′≤M) (rename-pres-≤ N′≤N)
rename-pres-≤ (≤-if⋆ L′≤L M′≤M N′≤N) = ≤-if⋆ (rename-pres-≤ L′≤L) (rename-pres-≤ M′≤M) (rename-pres-≤ N′≤N)
rename-pres-≤ (≤-ref M′≤M) = ≤-ref (rename-pres-≤ M′≤M)
rename-pres-≤ (≤-ref? M′≤M) = ≤-ref? (rename-pres-≤ M′≤M)
rename-pres-≤ (≤-deref M′≤M) = ≤-deref (rename-pres-≤ M′≤M)
rename-pres-≤ (≤-deref⋆ M′≤M) = ≤-deref⋆ (rename-pres-≤ M′≤M)
rename-pres-≤ (≤-assign L′≤L M′≤M) = ≤-assign (rename-pres-≤ L′≤L) (rename-pres-≤ M′≤M)
rename-pres-≤ (≤-assign? L′≤L M′≤M) = ≤-assign? (rename-pres-≤ L′≤L) (rename-pres-≤ M′≤M)
rename-pres-≤ (≤-prot x M′≤M) = ≤-prot x (rename-pres-≤ M′≤M)


ext-pres-≤ˢ : ∀ {Γ} {A} {σ : CC2.Statics.Subst} {σ′ : Dyn.Syntax.Subst}
  → σ′ ≤ˢ σ ⇐ Γ
    --------------------------------------------------------------------------
  → (ext σ′) ≤ˢ ext σ ⇐ (A ∷ Γ)
ext-pres-≤ˢ {Γ} σ′≤σ zero Γ∋x⦂A A≋B = ≤-var
ext-pres-≤ˢ {Γ} σ′≤σ (suc x) Γ∋x⦂A A≋B = rename-pres-≤ (σ′≤σ _ Γ∋x⦂A A≋B)


subst-pres-≤ : ∀ {Γ Σ g ℓ} {A B} {M M′} {σ : CC2.Statics.Subst} {σ′ : Dyn.Syntax.Subst}
  → Γ ; Σ ; g ; ℓ ⊢ M ⇐ A
  → σ′ ≤ˢ σ ⇐ Γ
  → M′ ≤ M ⇐ B
  → A ≋ B
    --------------------------------------------------------------------
  → ⟪ σ′ ⟫ M′ ≤ ⦅ σ ⦆ M ⇐ B
subst-pres-≤ (⊢var Γ∋x⦂A) σ′≤σ ≤-var A≋B = σ′≤σ _ Γ∋x⦂A A≋B
subst-pres-≤ ⊢M σ′≤σ (≤-const x) _ = ≤-const x
subst-pres-≤ ⊢M σ′≤σ (≤-wrapped-const x y z) _ = ≤-wrapped-const x y z
subst-pres-≤ (⊢lam ⊢M) σ′≤σ (≤-lam M′≤M x) (sim-fun _ B₁≋B₂) = ≤-lam (subst-pres-≤ {ℓ = low} ⊢M (ext-pres-≤ˢ σ′≤σ) M′≤M B₁≋B₂) x
subst-pres-≤ (⊢cast (⊢lam ⊢M)) σ′≤σ (≤-wrapped-lam M′≤M 𝓋 x) sim =
  ≤-wrapped-lam (subst-pres-≤ {ℓ = low} ⊢M (ext-pres-≤ˢ σ′≤σ) M′≤M ≋-refl) 𝓋 x
subst-pres-≤ ⊢M σ′≤σ (≤-addr x) sim = ≤-addr x
subst-pres-≤ ⊢M σ′≤σ (≤-wrapped-addr 𝓋 x) sim = ≤-wrapped-addr 𝓋 x
subst-pres-≤ (⊢app ⊢M ⊢N _) σ′≤σ (≤-app M′≤M N′≤N) sim =
  ≤-app (subst-pres-≤ ⊢M σ′≤σ M′≤M (sim-fun ≋-refl ≋-refl)) (subst-pres-≤ ⊢N σ′≤σ N′≤N ≋-refl)
subst-pres-≤ (⊢app⋆ ⊢M ⊢N) σ′≤σ (≤-app⋆ M′≤M N′≤N) sim = ≤-app⋆ (subst-pres-≤ ⊢M σ′≤σ M′≤M ≋-refl) (subst-pres-≤ ⊢N σ′≤σ N′≤N ≋-refl)
subst-pres-≤ (⊢if ⊢L ⊢M ⊢N _) σ′≤σ (≤-if L′≤L M′≤M N′≤N) sim =
  ≤-if (subst-pres-≤ ⊢L σ′≤σ L′≤L ≋-refl) (subst-pres-≤ {ℓ = low} ⊢M σ′≤σ M′≤M ≋-refl) (subst-pres-≤ {ℓ = low} ⊢N σ′≤σ N′≤N ≋-refl)
subst-pres-≤ (⊢if⋆ ⊢L ⊢M ⊢N) σ′≤σ (≤-if⋆ L′≤L M′≤M N′≤N) sim =
  ≤-if⋆ (subst-pres-≤ ⊢L σ′≤σ L′≤L ≋-refl) (subst-pres-≤ {ℓ = low} ⊢M σ′≤σ M′≤M ≋-refl) (subst-pres-≤ {ℓ = low} ⊢N σ′≤σ N′≤N ≋-refl)
subst-pres-≤ (⊢ref ⊢M _) σ′≤σ (≤-ref M′≤M) (sim-ref A≋B) = ≤-ref (subst-pres-≤ ⊢M σ′≤σ M′≤M A≋B)
subst-pres-≤ (⊢ref? ⊢M) σ′≤σ (≤-ref? M′≤M) (sim-ref A≋B) = ≤-ref? (subst-pres-≤ ⊢M σ′≤σ M′≤M A≋B)
subst-pres-≤ (⊢deref ⊢M _) σ′≤σ (≤-deref M′≤M) sim = ≤-deref (subst-pres-≤ ⊢M σ′≤σ M′≤M ≋-refl)
subst-pres-≤ (⊢deref⋆ ⊢M) σ′≤σ (≤-deref⋆ M′≤M) sim = ≤-deref⋆ (subst-pres-≤ ⊢M σ′≤σ M′≤M ≋-refl)
subst-pres-≤ (⊢assign ⊢L ⊢M _ _) σ′≤σ (≤-assign L′≤L M′≤M) sim =
  ≤-assign (subst-pres-≤ ⊢L σ′≤σ L′≤L ≋-refl) (subst-pres-≤ ⊢M σ′≤σ M′≤M ≋-refl)
subst-pres-≤ (⊢assign? ⊢L ⊢M) σ′≤σ (≤-assign? L′≤L M′≤M) sim =
  ≤-assign? (subst-pres-≤ ⊢L σ′≤σ L′≤L ≋-refl) (subst-pres-≤ ⊢M σ′≤σ M′≤M ≋-refl)
subst-pres-≤ (⊢prot ⊢M _ _ _) σ′≤σ (≤-prot x M′≤M) sim = ≤-prot x (subst-pres-≤ ⊢M σ′≤σ M′≤M ≋-refl)
