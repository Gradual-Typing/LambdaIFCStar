open import Common.Types

module Security.SubstPres where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
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


pc-typing-uniq : ∀ {g₁ g₂} {PC : LExpr} → (v : LVal PC) → ⊢ PC ⇐ g₁ → ⊢ PC ⇐ g₂ → g₁ ≡ g₂
pc-typing-uniq v-l ⊢l ⊢l = refl
pc-typing-uniq (v-cast x) (⊢cast ⊢l) (⊢cast ⊢l) = refl


_≤ˢ_⇐_ : ∀ (σ′ : Dyn.Syntax.Subst) (σ : CC2.Statics.Subst) → (Γ : Context) → Set
σ′ ≤ˢ σ ⇐ Γ =
  (∀ x {A}
    → Γ ∋ x ⦂ A
    → (∀ {g} → g ⊢ σ′ x ≤ σ x ⇐ A))

rename-pres-≤ : ∀ {gc A} {M M′} {ρ : Rename}
  → gc ⊢ M′ ≤ M ⇐ A
    -----------------------------------------------------------------------------
  → gc ⊢ Dyn.Syntax.rename ρ M′ ≤ CC2.Statics.rename ρ M ⇐ A
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
rename-pres-≤ (≤-cast M′≤M) = ≤-cast (rename-pres-≤ M′≤M)
rename-pres-≤ (≤-prot x M′≤M y) = ≤-prot x (rename-pres-≤ M′≤M) y


ext-pres-≤ˢ : ∀ {Γ} {A} {σ : CC2.Statics.Subst} {σ′ : Dyn.Syntax.Subst}
  → σ′ ≤ˢ σ ⇐ Γ
    --------------------------------------------------------------------------
  → (ext σ′) ≤ˢ ext σ ⇐ (A ∷ Γ)
ext-pres-≤ˢ {Γ} σ′≤σ zero Γ∋x⦂A = ≤-var
ext-pres-≤ˢ {Γ} σ′≤σ (suc x) Γ∋x⦂A = rename-pres-≤ (σ′≤σ _ Γ∋x⦂A)


subst-pres-≤ : ∀ {Γ Σ g ℓ} {A} {M M′} {σ : CC2.Statics.Subst} {σ′ : Dyn.Syntax.Subst}
  → Γ ; Σ ; g ; ℓ ⊢ M ⇐ A
  → σ′ ≤ˢ σ ⇐ Γ
  → g ⊢ M′ ≤ M ⇐ A
    --------------------------------------------------------------------
  → g ⊢ ⟪ σ′ ⟫ M′ ≤ ⦅ σ ⦆ M ⇐ A
subst-pres-≤ (⊢var Γ∋x⦂A) σ′≤σ ≤-var = σ′≤σ _ Γ∋x⦂A
subst-pres-≤ ⊢M σ′≤σ (≤-const x) = ≤-const x
subst-pres-≤ ⊢M σ′≤σ (≤-wrapped-const x y z) = ≤-wrapped-const x y z
subst-pres-≤ (⊢lam ⊢M) σ′≤σ (≤-lam M′≤M x) = ≤-lam (subst-pres-≤ {ℓ = low} ⊢M (ext-pres-≤ˢ σ′≤σ) M′≤M) x
subst-pres-≤ (⊢cast (⊢lam ⊢M)) σ′≤σ (≤-wrapped-lam M′≤M 𝓋 x) =
  ≤-wrapped-lam (subst-pres-≤ {ℓ = low} ⊢M (ext-pres-≤ˢ σ′≤σ) M′≤M) 𝓋 x
subst-pres-≤ ⊢M σ′≤σ (≤-addr x) = ≤-addr x
subst-pres-≤ ⊢M σ′≤σ (≤-wrapped-addr 𝓋 x) = ≤-wrapped-addr 𝓋 x
subst-pres-≤ (⊢app ⊢M ⊢N _) σ′≤σ (≤-app M′≤M N′≤N) =
  ≤-app (subst-pres-≤ ⊢M σ′≤σ M′≤M ) (subst-pres-≤ ⊢N σ′≤σ N′≤N)
subst-pres-≤ (⊢app⋆ ⊢M ⊢N) σ′≤σ (≤-app⋆ M′≤M N′≤N) = ≤-app⋆ (subst-pres-≤ ⊢M σ′≤σ M′≤M) (subst-pres-≤ ⊢N σ′≤σ N′≤N)
subst-pres-≤ (⊢if ⊢L ⊢M ⊢N _) σ′≤σ (≤-if L′≤L M′≤M N′≤N) =
  ≤-if (subst-pres-≤ ⊢L σ′≤σ L′≤L) (subst-pres-≤ {ℓ = low} ⊢M σ′≤σ M′≤M) (subst-pres-≤ {ℓ = low} ⊢N σ′≤σ N′≤N)
subst-pres-≤ (⊢if⋆ ⊢L ⊢M ⊢N) σ′≤σ (≤-if⋆ L′≤L M′≤M N′≤N) =
  ≤-if⋆ (subst-pres-≤ ⊢L σ′≤σ L′≤L) (subst-pres-≤ {ℓ = low} ⊢M σ′≤σ M′≤M) (subst-pres-≤ {ℓ = low} ⊢N σ′≤σ N′≤N)
subst-pres-≤ (⊢ref ⊢M _) σ′≤σ (≤-ref M′≤M) = ≤-ref (subst-pres-≤ ⊢M σ′≤σ M′≤M)
subst-pres-≤ (⊢ref? ⊢M) σ′≤σ (≤-ref? M′≤M) = ≤-ref? (subst-pres-≤ ⊢M σ′≤σ M′≤M)
subst-pres-≤ (⊢deref ⊢M _) σ′≤σ (≤-deref M′≤M) = ≤-deref (subst-pres-≤ ⊢M σ′≤σ M′≤M)
subst-pres-≤ (⊢deref⋆ ⊢M) σ′≤σ (≤-deref⋆ M′≤M) = ≤-deref⋆ (subst-pres-≤ ⊢M σ′≤σ M′≤M)
subst-pres-≤ (⊢assign ⊢L ⊢M _ _) σ′≤σ (≤-assign L′≤L M′≤M) =
  ≤-assign (subst-pres-≤ ⊢L σ′≤σ L′≤L ) (subst-pres-≤ ⊢M σ′≤σ M′≤M)
subst-pres-≤ (⊢assign? ⊢L ⊢M) σ′≤σ (≤-assign? L′≤L M′≤M) =
  ≤-assign? (subst-pres-≤ ⊢L σ′≤σ L′≤L) (subst-pres-≤ ⊢M σ′≤σ M′≤M)
subst-pres-≤ (⊢cast ⊢M ) σ′≤σ (≤-cast M′≤M) = ≤-cast (subst-pres-≤ ⊢M σ′≤σ M′≤M)
subst-pres-≤ (⊢prot {vc = v} ⊢M ⊢PC† _ _) σ′≤σ (≤-prot x M′≤M ⊢PC)
  rewrite pc-typing-uniq v ⊢PC ⊢PC† = ≤-prot x (subst-pres-≤ ⊢M σ′≤σ M′≤M) ⊢PC†


substitution-pres-≤ : ∀ {Γ Σ g ℓ} {A B} {M M′ V V′}
  → B ∷ Γ ; Σ ; g ; ℓ ⊢ M ⇐ A
  → g ⊢ M′ ≤ M ⇐ A
  → (∀ {g} → g ⊢ V′ ≤ V ⇐ B)
    --------------------------------------------------------------------
  → g ⊢ (Dyn.Syntax._[_] M′ V′) ≤ (CC2.Statics._[_] M V) ⇐ A
substitution-pres-≤ ⊢M M′≤M V′≤V = subst-pres-≤ ⊢M ♣ M′≤M
  where
  ♣ : _
  ♣ 0 refl = V′≤V
  ♣ (suc n) x = ≤-var
