module Compile where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)

open import Syntax

open import BlameLabels
open import Types
open import TypeBasedCast
open import SurfaceLang
  renaming (`_ to `ᴳ_;
            $_of_ to $ᴳ_of_;
            ƛ[_]_˙_of_ to ƛᴳ[_]_˙_of_;
            !_ to !ᴳ_)
open import CC renaming (Term to CCTerm)
open import Preservation using (rename-↑1-pres)
open import Utils


compile : ∀ {Γ gc A} (M : Term) → Γ ; gc ⊢ᴳ M ⦂ A → CCTerm
compile ($ᴳ k of ℓ) ⊢const = $ k of ℓ
compile (`ᴳ x) (⊢var x∈Γ) = ` x
compile (ƛᴳ[ pc ] A ˙ N of ℓ) (⊢lam ⊢N) = ƛ[ pc ] A ˙ compile N ⊢N of ℓ
compile (L · M at p) (⊢app {gc = gc} {gc′} {A = A} {A′} {B} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′) =
  case ⟨ ≲-prop A′≲A , ≾-prop′ gc≾gc′ , ≾-prop′ g≾gc′ ⟩ of λ where
  ⟨ ⟨ C , A′~C , C<:A ⟩ , ⟨ g₁ , gc<:g₁ , g₁~gc′ ⟩ , ⟨ g₂ , g<:g₂ , g₂~gc′ ⟩ ⟩ →
    let g₁⋎g₂~gc′ = subst (λ □ → _ ~ₗ □) g⋎̃g≡g (consis-join-~ₗ g₁~gc′ g₂~gc′)
        c~ = ~-ty ~ₗ-refl (~-fun (~ₗ-sym g₁⋎g₂~gc′) ~-refl ~-refl)
        c = cast ([ gc′ ] A ⇒ B of g) ([ g₁ ⋎̃ g₂ ] A ⇒ B of g) p c~ in
    (compile L ⊢L ⟨ c ⟩) · (compile M ⊢M ⟨ cast A′ C p A′~C ⟩)
compile (if L then M else N at p) (⊢if {A = A} {B} {C} ⊢L ⊢M ⊢N A∨̃B≡C) =
  case consis-join-≲-inv {A} {B} A∨̃B≡C of λ where
  ⟨ A≲C , B≲C ⟩ →
    case ⟨ ≲-prop A≲C , ≲-prop B≲C ⟩ of λ where
    ⟨ ⟨ A′ , A~A′ , A′<:C ⟩ , ⟨ B′ , B~B′ , B′<:C ⟩ ⟩ →
      if (compile L ⊢L) C
         (compile M ⊢M ⟨ cast A A′ p A~A′ ⟩)
         (compile N ⊢N ⟨ cast B B′ p B~B′ ⟩)
compile (M ꞉ A at p) (⊢ann {A′ = A′} ⊢M A′≲A) =
  case ≲-prop A′≲A of λ where
  ⟨ B , A′~B , B<:A ⟩ →
    compile M ⊢M ⟨ cast A′ B p A′~B ⟩
compile (ref[ ℓ ] M at p) (⊢ref {gc = gc} {T = T} {g} ⊢M Tg≲Tℓ gc≾ℓ) =
  case ≲-prop Tg≲Tℓ of λ where
  ⟨ A , Tg~A , A<:Tℓ ⟩ →
    let M′ = compile M ⊢M
        M″ = M′ ⟨ cast (T of g) A p Tg~A ⟩ in
    case gc≾ℓ of λ where
    ≾-⋆l       → ref?[ ℓ ] M″
    (≾-l ℓᶜ≼ℓ) →  ref[ ℓ ] M″
compile (!ᴳ M) (⊢deref ⊢M) = ! (compile M ⊢M)
compile (L := M at p) (⊢assign {gc = gc} {A = A} {T} {g} {g₁} ⊢L ⊢M A≲Tg1 g≾g1 gc≾g1) =
  case ⟨ ≲-prop A≲Tg1 , ≾-prop g≾g1 ⟩ of λ where
  ⟨ ⟨ B , A~B , B<:Tg1 ⟩ , ⟨ g₂ , g~g₂ , g₂<:g₁ ⟩ ⟩ →
    let L′ = compile L ⊢L
        L″ = L′ ⟨ cast (Ref (T of g₁) of g) (Ref (T of g₁) of g₂) p (~-ty g~g₂ ~ᵣ-refl) ⟩
        M′ = compile M ⊢M
        M″ = M′ ⟨ cast A B p A~B ⟩ in
    case gc≾g1 of λ where
    (≾-l ℓᶜ≼ℓ₁) → L″ :=  M″
    _           → L″ :=? M″


compile-preserve : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
  → (∀ {pc} → Γ ; ∅ ; gc ; pc ⊢ compile M ⊢M ⦂ A)
compile-preserve ($ᴳ k of ℓ) ⊢const = ⊢const
compile-preserve (`ᴳ x) (⊢var Γ∋x) = ⊢var Γ∋x
compile-preserve (ƛᴳ[ pc ] A ˙ N of ℓ) (⊢lam ⊢N) = ⊢lam (compile-preserve N ⊢N)
compile-preserve (L · M at p) (⊢app {gc = gc} {gc′} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′)
  with ≲-prop A′≲A | ≾-prop′ gc≾gc′ | ≾-prop′ g≾gc′
... | ⟨ B , A′~B , B<:A ⟩ | ⟨ g₁ , gc<:g₁ , g₁~gc′ ⟩ | ⟨ g₂ , g<:g₂ , g₂~gc′ ⟩ =
  ⊢app (⊢sub (⊢cast (compile-preserve L ⊢L))
             (<:-ty <:ₗ-refl (<:-fun (consis-join-<:ₗ gc<:g₁ g<:g₂) <:-refl <:-refl)))
       (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:A)
compile-preserve (if L then M else N at p) (⊢if {A = A} {B} {C} ⊢L ⊢M ⊢N A∨̃B≡C)
  with consis-join-≲-inv {A} {B} A∨̃B≡C
... | ⟨ A≲C , B≲C ⟩
  with ≲-prop A≲C | ≲-prop B≲C
... | ⟨ A′ , A~A′ , A′<:C ⟩ | ⟨ B′ , B~B′ , B′<:C ⟩ =
  ⊢if (compile-preserve L ⊢L)
      (⊢sub (⊢cast (compile-preserve M ⊢M)) A′<:C)
      (⊢sub (⊢cast (compile-preserve N ⊢N)) B′<:C)
compile-preserve {Γ} {Σ} {A = A} (M ꞉ A at p) (⊢ann {A′ = A′} ⊢M A′≲A)
  with ≲-prop A′≲A
... | ⟨ B , A′~B , B<:A ⟩ = ⊢sub (⊢cast (compile-preserve M ⊢M)) B<:A
compile-preserve (ref[ ℓ ] M at p) (⊢ref {gc = gc} ⊢M Tg≲Tℓ gc≾ℓ)
  with ≲-prop Tg≲Tℓ
... | ⟨ A , Tg~A , A<:Tℓ ⟩
  with gc≾ℓ
...   | ≾-⋆l     = ⊢ref? (⊢sub (⊢cast (compile-preserve M ⊢M)) A<:Tℓ)
...   | ≾-l ℓᶜ≼ℓ = {- gc = ℓᶜ -}
  ⊢ref (⊢sub (⊢cast (compile-preserve M ⊢M)) A<:Tℓ) ℓᶜ≼ℓ
compile-preserve (!ᴳ M) (⊢deref ⊢M) = ⊢deref (compile-preserve M ⊢M)
compile-preserve (L := M at p) (⊢assign {gc = gc} {g = g} {g₁} ⊢L ⊢M A≲Tg1 g≾g1 gc≾g1)
  with ≲-prop A≲Tg1 | ≾-prop g≾g1
... | ⟨ B , A~B , B<:Tg1 ⟩ | ⟨ g₂ , g~g₂ , g₂<:g₁ ⟩
  with gc≾g1
...   | ≾-l ℓᶜ≼ℓ₁ = {- gc = ℓᶜ and g₁ = ℓ₁ -}
  ⊢assign (⊢sub (⊢cast (compile-preserve L ⊢L)) (<:-ty g₂<:g₁ <:ᵣ-refl))
          (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:Tg1)
          ℓᶜ≼ℓ₁
...   | ≾-⋆l =
  ⊢assign? (⊢sub (⊢cast (compile-preserve L ⊢L)) (<:-ty g₂<:g₁ <:ᵣ-refl))
           (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:Tg1)
...   | ≾-⋆r =
  ⊢assign? (⊢sub (⊢cast (compile-preserve L ⊢L)) (<:-ty g₂<:g₁ <:ᵣ-refl))
           (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:Tg1)

{- Compilation from Surface to CC is type-preserving. -}
compilation-preserves-type : ∀ {Γ gc A} (M : Term)
  → (⊢M : Γ ; gc ⊢ᴳ M ⦂ A)
  → Γ ; ∅ ; gc ; low ⊢ compile M ⊢M ⦂ A
compilation-preserves-type M ⊢M = compile-preserve M ⊢M {low}
