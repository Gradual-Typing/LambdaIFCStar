module CC2.CompilePrecision where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Function using (case_of_)

open import Syntax

open import Common.Utils
open import Common.BlameLabels
open import Common.Types
open import Common.TypeBasedCast
open import Common.CoercePrecision
open import Surface2.Lang
  renaming (`_ to `ᴳ_;
            $_of_ to $ᴳ_of_)
open import Surface2.Typing
open import Surface2.Precision

open import CC2.Syntax public  renaming (Term to CCTerm)
open import CC2.Typing public
open import CC2.Precision
open import CC2.Compile


compile-pres-precision : ∀ {Γ Γ′ g g′ M M′ A A′}
  → Γ ⊑* Γ′
  → g ⊑ₗ g′
  → ⊢ M ⊑ᴳ M′
  → (⊢M  : Γ  ; g  ⊢ᴳ M  ⦂ A )
  → (⊢M′ : Γ′ ; g′ ⊢ᴳ M′ ⦂ A′)
    --------------------------------------------------------------------------------------------
  → (∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ g ; g′ ∣ ℓ ; ℓ′ ⊢ compile M ⊢M ⊑ compile M′ ⊢M′ ⇐ A ⊑ A′)
compile-pres-precision Γ⊑Γ′ g⊑g′ ⊑ᴳ-const ⊢const ⊢const = ⊑-const
compile-pres-precision Γ⊑Γ′ g⊑g′ ⊑ᴳ-var (⊢var Γ∋x⦂A) (⊢var Γ′∋x⦂A′) = ⊑-var Γ∋x⦂A Γ′∋x⦂A′
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-lam x x₁ M⊑M′) ⊢M ⊢M′ = {!!}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-app M⊑M′ M⊑M′₁) ⊢M ⊢M′ = {!!}
{- Compiling If -}
compile-pres-precision Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-if L⊑L′ M⊑M′ N⊑N′)
    (⊢if {gc = gc}  {A = A}  {B}  {C}  {g = g}  ⊢L  ⊢M  ⊢N  A∨̃B≡C)
    (⊢if {gc = gc′} {A = A′} {B′} {C′} {g = g′} ⊢L′ ⊢M′ ⊢N′ A′∨̃B′≡C′)
  with compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′
... | 𝒞L⊑𝒞L′
  with cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′
... | ⟨ _ , _ , ⊑-ty g⊑g′ ⊑-ι ⟩
  with compile-pres-precision Γ⊑Γ′ (consis-join-⊑ₗ gc⊑gc′ g⊑g′) M⊑M′ ⊢M ⊢M′
     | compile-pres-precision Γ⊑Γ′ (consis-join-⊑ₗ gc⊑gc′ g⊑g′) N⊑N′ ⊢N ⊢N′
... | 𝒞M⊑𝒞M′ | 𝒞N⊑𝒞N′
  with cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′
     | cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞N⊑𝒞N′
... | ⟨ _ , _ , A⊑A′ ⟩ | ⟨ _ , _ , B⊑B′ ⟩
  with consis-join-≲-inv {A} {B} A∨̃B≡C | consis-join-≲-inv {A′} {B′} A′∨̃B′≡C′
... | ⟨ A≲C , B≲C ⟩ | ⟨ A′≲C′ , B′≲C′ ⟩
  with gc | g | gc′ | g′ | C | C′ | g⊑g′ | gc⊑gc′
... | l _ | l ℓ | l _ | l ℓ′ | _ | _ | l⊑l | l⊑l =
  ⊑-if (compile-pres-precision Γ⊑Γ′ l⊑l L⊑L′ ⊢L ⊢L′)
       (⊑-cast (compile-pres-precision Γ⊑Γ′ ⊑ₗ-refl M⊑M′ ⊢M ⊢M′)
               (coerce-prec A⊑A′ (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′) A≲C A′≲C′))
       (⊑-cast (compile-pres-precision Γ⊑Γ′ ⊑ₗ-refl N⊑N′ ⊢N ⊢N′)
               (coerce-prec B⊑B′ (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′) B≲C B′≲C′))
       refl refl
... | l _ | ⋆ | l _ | l ℓ′ | T of ⋆ | T′ of g₁ | ⋆⊑ | l⊑l =
  let C⊑C′ : T of ⋆ ⊑ T′ of g₁
      C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
      prec : stamp (T of ⋆) ⋆ ⊑ stamp (T′ of g₁) (l ℓ′)
      prec = stamp-⊑ C⊑C′ ⋆⊑ in
  case C⊑C′ of λ where
  (⊑-ty ℓ⊑g₁ T⊑T′) →
    ⊑-castl (⊑-if⋆l (⊑-castl (compile-pres-precision Γ⊑Γ′ l⊑l L⊑L′ ⊢L ⊢L′) (inject-prec-left (⊑-ty ⋆⊑ ⊑-ι)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′) (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ N⊑N′ ⊢N ⊢N′) (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′))) refl) (coerce-prec-left prec prec (≲-ty ≾-⋆l _))
... | l _ | ⋆ | l _ | l ℓ′ | T of l ℓ | T′ of g₁ | ⋆⊑ | l⊑l =
  let C⊑C′ : T of l ℓ ⊑ T′ of g₁
      C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
      prec : stamp (T of l ℓ) ⋆ ⊑ stamp (T′ of g₁) (l ℓ′)
      prec = stamp-⊑ C⊑C′ ⋆⊑ in
  case C⊑C′ of λ where
  (⊑-ty ℓ⊑g₁ T⊑T′) →
    ⊑-castl (⊑-if⋆l (⊑-castl (compile-pres-precision Γ⊑Γ′ l⊑l L⊑L′ ⊢L ⊢L′) (inject-prec-left (⊑-ty ⋆⊑ ⊑-ι)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′) (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ N⊑N′ ⊢N ⊢N′) (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′))) refl) (coerce-prec-left prec prec (≲-ty ≾-⋆l _))
... | ⋆ | l _ | l _ | l ℓ′ | T of ⋆ | T′ of g₁ | l⊑l | ⋆⊑ =
  let C⊑C′ : T of ⋆ ⊑ T′ of g₁
      C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
      prec : stamp (T of ⋆) ⋆ ⊑ stamp (T′ of g₁) (l ℓ′)
      prec = stamp-⊑ C⊑C′ ⋆⊑ in
  case C⊑C′ of λ where
  (⊑-ty ℓ⊑g₁ T⊑T′) →
    ⊑-castl (⊑-if⋆l (⊑-castl (compile-pres-precision Γ⊑Γ′ ⋆⊑ L⊑L′ ⊢L ⊢L′) (inject-prec-left (⊑-ty l⊑l ⊑-ι)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′) (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ N⊑N′ ⊢N ⊢N′) (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′))) refl) (coerce-prec-left prec prec (≲-ty ≾-⋆l _))
... | ⋆ | l _ | l _ | l ℓ′ | T of l ℓ | T′ of g₁ | l⊑l | ⋆⊑ =
  let C⊑C′ : T of l ℓ ⊑ T′ of g₁
      C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
      prec₁ : stamp (T of l ℓ) ⋆ ⊑ stamp (T′ of g₁) (l ℓ′)
      prec₁ = stamp-⊑ C⊑C′ ⋆⊑
      prec₂ : stamp (T of l ℓ) (l ℓ′) ⊑ stamp (T′ of g₁) (l ℓ′)
      prec₂ = stamp-⊑ C⊑C′ l⊑l in
  case C⊑C′ of λ where
  (⊑-ty ℓ⊑g₁ T⊑T′) →
    ⊑-castl (⊑-if⋆l (⊑-castl (compile-pres-precision Γ⊑Γ′ ⋆⊑ L⊑L′ ⊢L ⊢L′) (inject-prec-left (⊑-ty l⊑l ⊑-ι)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′) (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ N⊑N′ ⊢N ⊢N′) (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′))) refl) (coerce-prec-left prec₁ prec₂ (≲-ty ≾-⋆l _))
... | ⋆ | ⋆ | l _ | l ℓ′ | T of ⋆ | T′ of g₁ | ⋆⊑ | ⋆⊑ =
  let C⊑C′ : T of ⋆ ⊑ T′ of g₁
      C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
      prec : stamp (T of ⋆) ⋆ ⊑ stamp (T′ of g₁) (l ℓ′)
      prec = stamp-⊑ C⊑C′ ⋆⊑ in
  case C⊑C′ of λ where
  (⊑-ty ℓ⊑g₁ T⊑T′) →
    ⊑-castl (⊑-if⋆l (⊑-castl (compile-pres-precision Γ⊑Γ′ ⋆⊑ L⊑L′ ⊢L ⊢L′) (inject-prec-left (⊑-ty ⋆⊑ ⊑-ι)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′) (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ N⊑N′ ⊢N ⊢N′) (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′))) refl) (coerce-prec-left prec prec (≲-ty ≾-⋆l _))
... | ⋆ | ⋆ | l _ | l ℓ′ | T of l ℓ | T′ of g₁ | ⋆⊑ | ⋆⊑ =
  let C⊑C′ : T of l ℓ ⊑ T′ of g₁
      C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
      prec : stamp (T of l ℓ) ⋆ ⊑ stamp (T′ of g₁) (l ℓ′)
      prec = stamp-⊑ C⊑C′ ⋆⊑ in
  case C⊑C′ of λ where
  (⊑-ty ℓ⊑g₁ T⊑T′) →
    ⊑-castl (⊑-if⋆l (⊑-castl (compile-pres-precision Γ⊑Γ′ ⋆⊑ L⊑L′ ⊢L ⊢L′) (inject-prec-left (⊑-ty ⋆⊑ ⊑-ι)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′) (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′)))
                    (⊑-castl (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ N⊑N′ ⊢N ⊢N′) (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                             (inject-prec-left (⊑-ty ℓ⊑g₁ T⊑T′))) refl) (coerce-prec-left prec prec (≲-ty ≾-⋆l _))
... | l _ | ⋆ | l _ | ⋆ | T of ⋆ | T′ of ⋆ | ⋆⊑ | l⊑l =
  let C⊑C′ : T of ⋆ ⊑ T′ of ⋆
      C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′) in
  ⊑-cast (⊑-if⋆ (⊑-cast (compile-pres-precision Γ⊑Γ′ l⊑l L⊑L′ ⊢L ⊢L′) (inject-prec ⊑-refl))
                (⊑-cast (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′)
                                (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                        (inject-prec C⊑C′))
                (⊑-cast (⊑-cast (compile-pres-precision Γ⊑Γ′ ⋆⊑ N⊑N′ ⊢N ⊢N′)
                                (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                        (inject-prec C⊑C′)))
         (coerce-prec C⊑C′ C⊑C′ (≲-ty ≾-⋆l _) (≲-ty ≾-⋆l _))
... | l _ | ⋆ | l _ | ⋆ | T of ⋆ | T′ of l ℓ | ⋆⊑ | l⊑l = {!!}
  -- let C⊑C′ : T of g₁ ⊑ T′ of g₂
  --     C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
  --     prec : stamp (T of g₁) ⋆ ⊑ stamp (T′ of g₂) ⋆
  --     prec = stamp-⊑ C⊑C′ ⋆⊑ in
  -- ⊑-cast {!⊑-if⋆!} (coerce-prec prec prec _ _)
... | l _ | ⋆ | l _ | ⋆ | T of l ℓ | T′ of ⋆ | ⋆⊑ | l⊑l = {!!}
  -- let C⊑C′ : T of g₁ ⊑ T′ of g₂
  --     C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
  --     prec : stamp (T of g₁) ⋆ ⊑ stamp (T′ of g₂) ⋆
  --     prec = stamp-⊑ C⊑C′ ⋆⊑ in
  -- ⊑-cast {!⊑-if⋆!} (coerce-prec prec prec _ _)
... | l _ | ⋆ | l _ | ⋆ | T of l ℓ₁ | T′ of l ℓ₂ | ⋆⊑ | l⊑l = {!!}
  -- let C⊑C′ : T of g₁ ⊑ T′ of g₂
  --     C⊑C′ = (consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′)
  --     prec : stamp (T of g₁) ⋆ ⊑ stamp (T′ of g₂) ⋆
  --     prec = stamp-⊑ C⊑C′ ⋆⊑ in
  -- ⊑-cast {!⊑-if⋆!} (coerce-prec prec prec _ _)
... | ⋆ | l ℓ | ⋆ | l ℓ′ | _ | _ | l⊑l | ⋆⊑ = {!!}
... | ⋆ | ⋆ | ⋆ | l ℓ′ | _ | _ | ⋆⊑ | ⋆⊑ = {!!}
... | ⋆ | ⋆ | l _ | ⋆ | _ | _ | ⋆⊑ | ⋆⊑ = {!!}
... | ⋆ | ⋆ | ⋆ | ⋆ | _ | _ | ⋆⊑ | ⋆⊑ = {!!}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-ann M⊑M′ A⊑A′) (⊢ann ⊢M B≲A) (⊢ann ⊢M′ B′≲A′) =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ g⊑g′ M⊑M′ ⊢M ⊢M′ in
  let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ in
  ⊑-cast 𝒞M⊑𝒞M′ (coerce-prec B⊑B′ A⊑A′ B≲A B′≲A′)
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-let M⊑M′ M⊑M′₁) ⊢M ⊢M′ = {!!}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-ref M⊑M′) ⊢M ⊢M′ = {!!}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-deref M⊑M′) ⊢M ⊢M′ = {!!}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-assign M⊑M′ M⊑M′₁) ⊢M ⊢M′ = {!!}
