module Compile.Precision.CompilePrecision where

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym)
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


{- Here is the lemma statement of "compilation preserves precision" -}
compile-pres-precision : ∀ {Γ Γ′ g g′ M M′ A A′}
  → Γ ⊑* Γ′
  → g ⊑ₗ g′
  → ⊢ M ⊑ᴳ M′
  → (⊢M  : Γ  ; g  ⊢ᴳ M  ⦂ A )
  → (⊢M′ : Γ′ ; g′ ⊢ᴳ M′ ⦂ A′)
    --------------------------------------------------------------------------------------------
  → (∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ g ; g′ ∣ ℓ ; ℓ′ ⊢ compile M ⊢M ⊑ compile M′ ⊢M′ ⇐ A ⊑ A′)


{- There are four cases about compiling an if-conditional,
   depending on whether the labels on the two sides are all specific.
   So let's put them in a separate lemma. -}
private
  compile-pres-precision-if : ∀ {Γ Γ′ g g′ M M′ L L′ N₁ N₁′ N₂ N₂′ A A′} {p}
    → Γ ⊑* Γ′
    → g ⊑ₗ g′
    → ⊢ M ⊑ᴳ M′
    → (⊢M  : Γ  ; g  ⊢ᴳ M  ⦂ A )
    → (⊢M′ : Γ′ ; g′ ⊢ᴳ M′ ⦂ A′)
    → M  ≡ if L  then N₁  else N₂  at p
    → M′ ≡ if L′ then N₁′ else N₂′ at p
      --------------------------------------------------------------------------------------------
    → (∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ g ; g′ ∣ ℓ ; ℓ′ ⊢ compile M ⊢M ⊑ compile M′ ⊢M′ ⇐ A ⊑ A′)
compile-pres-precision-if {Γ} {Γ′} Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-if L⊑L′ M⊑M′ N⊑N′)
    (⊢if {gc = gc}  {A = A}  {B}  {C}  {g = g}  {p} ⊢L  ⊢M  ⊢N  A∨̃B≡C)
    (⊢if {gc = gc′} {A = A′} {B′} {C′} {g = g′} {p} ⊢L′ ⊢M′ ⊢N′ A′∨̃B′≡C′) eq eq′
  with consis-join-≲-inv {A} {B} A∨̃B≡C | consis-join-≲-inv {A′} {B′} A′∨̃B′≡C′
... | ⟨ A≲C , B≲C ⟩ | ⟨ A′≲C′ , B′≲C′ ⟩
  with C | C′
... | T of g₁ | T′ of g₂
  with all-specific? [ gc , g ] | all-specific? [ gc′ , g′ ]
... | yes (as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) as-nil))
    | yes (as-cons (＠ ℓ₁′) (as-cons (＠ ℓ₂′) as-nil)) =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  case ⟨ gc⊑gc′ , cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ ⟩ of λ where
  ⟨ l⊑l , _ , _ , ⊑-ty l⊑l ⊑-ι ⟩ →
    let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ ⊑ₗ-refl M⊑M′ ⊢M ⊢M′ in
    let 𝒞N⊑𝒞N′ = compile-pres-precision Γ⊑Γ′ ⊑ₗ-refl N⊑N′ ⊢N ⊢N′ in
    let ⟨ _ , _ , A⊑A′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ in
    let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞N⊑𝒞N′ in
    let C⊑C′ : T of g₁ ⊑ T′ of g₂
        C⊑C′ = consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′ in
    ⊑-if 𝒞L⊑𝒞L′
         (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec A⊑A′ C⊑C′ _ _))
         (⊑-cast 𝒞N⊑𝒞N′ (coerce-prec B⊑B′ C⊑C′ _ _)) refl refl
... | yes (as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) as-nil)) | no ¬as =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  case ⟨ gc⊑gc′ , cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ ⟩ of λ where
  ⟨ l⊑l {.ℓ₁} , _ , _ , ⊑-ty (l⊑l {.ℓ₂}) ⊑-ι ⟩ →
    let as = as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) as-nil) in
    contradiction as ¬as
... | no ¬as | yes (as-cons (＠ ℓ₁′) (as-cons (＠ ℓ₂′) as-nil)) =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ of λ where
  ⟨ _ , _ , ⊑-ty g⊑g′ ⊑-ι ⟩ →
    let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ (consis-join-⊑ₗ gc⊑gc′ g⊑g′) M⊑M′ ⊢M ⊢M′ in
    let 𝒞N⊑𝒞N′ = compile-pres-precision Γ⊑Γ′ (consis-join-⊑ₗ gc⊑gc′ g⊑g′) N⊑N′ ⊢N ⊢N′ in
    let ⟨ _ , _ , A⊑A′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ in
    let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞N⊑𝒞N′ in
    let C⊑C′ : T of g₁ ⊑ T′ of g₂
        C⊑C′ = consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′ in
    let ◆ₘ : ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ ⋆ ; _ ∣ ℓ ; ℓ′ ⊢ _ ⊑ _ ⇐ A ⊑ A′
        ◆ₘ = subst (λ □ →
                       ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ □ ; _ ∣ ℓ ; ℓ′ ⊢ compile _ ⊢M ⊑ compile _ ⊢M′ ⇐ A ⊑ A′)
                     (consis-join-not-all-specific ¬as) 𝒞M⊑𝒞M′ in
    let ◆ₙ : ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ ⋆ ; _ ∣ ℓ ; ℓ′ ⊢ _ ⊑ _ ⇐ B ⊑ B′
        ◆ₙ = subst (λ □ →
                       ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ □ ; _ ∣ ℓ ; ℓ′ ⊢ compile _ ⊢N ⊑ compile _ ⊢N′ ⇐ B ⊑ B′)
                     (consis-join-not-all-specific ¬as) 𝒞N⊑𝒞N′ in
    case C⊑C′ of λ where
    (⊑-ty g₁⊑g₂ T⊑T′) →
      let ♥ = ⊑-if⋆l (⊑-castl 𝒞L⊑𝒞L′ (inject-prec-left (⊑-ty g⊑g′ ⊑-ι)))
                     (⊑-castl (⊑-cast ◆ₘ (coerce-prec A⊑A′ C⊑C′ _ _)) (inject-prec-left (⊑-ty g₁⊑g₂ T⊑T′)))
                     (⊑-castl (⊑-cast ◆ₙ (coerce-prec B⊑B′ C⊑C′ _ _)) (inject-prec-left (⊑-ty g₁⊑g₂ T⊑T′)))
                     refl in
      ⊑-castl (subst (λ □ →
                        Γ ; Γ′ ∣ ∅ ; ∅ ∣ gc ; gc′ ∣ _ ; _ ⊢
                          if⋆ (compile _ ⊢L ⟨ inject (` Bool) g ⟩) T
                              ((compile _ ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g₁ ⟩)
                              ((compile _ ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g₁ ⟩) ⊑
                          if  (compile _ ⊢L′) (T′ of g₂) ℓ₂′
                              (compile _ ⊢M′ ⟨ coerce A′≲C′ p ⟩)
                              (compile _ ⊢N′ ⟨ coerce B′≲C′ p ⟩) ⇐ _ of □ ⊑ _)
               (sym g⋎̃⋆≡⋆) ♥)
              (coerce-prec-left (⊑-ty (consis-join-⊑ₗ g₁⊑g₂ ⋆⊑) T⊑T′)
                                (⊑-ty (consis-join-⊑ₗ g₁⊑g₂ g⊑g′) T⊑T′) _)
... | no ¬as | no ¬as′ =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ of λ where
  ⟨ _ , _ , ⊑-ty g⊑g′ ⊑-ι ⟩ →
    let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ (consis-join-⊑ₗ gc⊑gc′ g⊑g′) M⊑M′ ⊢M ⊢M′ in
    let 𝒞N⊑𝒞N′ = compile-pres-precision Γ⊑Γ′ (consis-join-⊑ₗ gc⊑gc′ g⊑g′) N⊑N′ ⊢N ⊢N′ in
    let ◆ₘ : ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ ⋆ ; ⋆ ∣ ℓ ; ℓ′ ⊢ _ ⊑ _ ⇐ A ⊑ A′
        ◆ₘ = subst₂ (λ □₁ □₂ →
                       ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ □₁ ; □₂ ∣ ℓ ; ℓ′ ⊢ compile _ ⊢M ⊑ compile _ ⊢M′ ⇐ A ⊑ A′)
                     (consis-join-not-all-specific ¬as) (consis-join-not-all-specific ¬as′) 𝒞M⊑𝒞M′ in
    let ◆ₙ : ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ ⋆ ; ⋆ ∣ ℓ ; ℓ′ ⊢ _ ⊑ _ ⇐ B ⊑ B′
        ◆ₙ = subst₂ (λ □₁ □₂ →
                       ∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ □₁ ; □₂ ∣ ℓ ; ℓ′ ⊢ compile _ ⊢N ⊑ compile _ ⊢N′ ⇐ B ⊑ B′)
                     (consis-join-not-all-specific ¬as) (consis-join-not-all-specific ¬as′) 𝒞N⊑𝒞N′ in
    let ⟨ _ , _ , A⊑A′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ in
    let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞N⊑𝒞N′ in
    let C⊑C′ : T of g₁ ⊑ T′ of g₂
        C⊑C′ = consis-join-⊑ A⊑A′ B⊑B′ A∨̃B≡C A′∨̃B′≡C′ in
    case C⊑C′ of λ where
    (⊑-ty g₁⊑g₂ T⊑T′) →
      let ♥ = ⊑-if⋆ (⊑-cast 𝒞L⊑𝒞L′ (inject-prec (⊑-ty g⊑g′ ⊑-ι)))
                     (⊑-cast (⊑-cast ◆ₘ (coerce-prec A⊑A′ C⊑C′ A≲C A′≲C′))
                             (inject-prec C⊑C′))
                     (⊑-cast (⊑-cast ◆ₙ (coerce-prec B⊑B′ C⊑C′ B≲C B′≲C′))
                             (inject-prec C⊑C′)) in
      ⊑-cast (subst₂ (λ □₁ □₂ →
                        Γ ; Γ′ ∣ ∅ ; ∅ ∣ gc ; gc′ ∣ _ ; _ ⊢
                          if⋆ (compile _ ⊢L ⟨ inject (` Bool) g ⟩) T
                              ((compile _ ⊢M ⟨ coerce A≲C p ⟩) ⟨ inject T g₁ ⟩)
                              ((compile _ ⊢N ⟨ coerce B≲C p ⟩) ⟨ inject T g₁ ⟩) ⊑
                          if⋆ (compile _ ⊢L′ ⟨ inject (` Bool) g′ ⟩) T′
                              ((compile _ ⊢M′ ⟨ coerce A′≲C′ p ⟩) ⟨ inject T′ g₂ ⟩)
                              ((compile _ ⊢N′ ⟨ coerce B′≲C′ p ⟩) ⟨ inject T′ g₂ ⟩)
                          ⇐ _ of □₁ ⊑ _ of □₂)
               (sym g⋎̃⋆≡⋆) (sym g⋎̃⋆≡⋆) ♥)
             (coerce-prec (⊑-ty (consis-join-⊑ₗ g₁⊑g₂ ⋆⊑  ) T⊑T′)
                          (⊑-ty (consis-join-⊑ₗ g₁⊑g₂ g⊑g′) T⊑T′) _ _)

private
  compile-pres-precision-app : ∀ {Γ Γ′ g g′ M M′ L L′ N N′ A A′} {p}
    → Γ ⊑* Γ′
    → g ⊑ₗ g′
    → ⊢ M ⊑ᴳ M′
    → (⊢M  : Γ  ; g  ⊢ᴳ M  ⦂ A )
    → (⊢M′ : Γ′ ; g′ ⊢ᴳ M′ ⦂ A′)
    → M  ≡ L  · N  at p
    → M′ ≡ L′ · N′ at p
      --------------------------------------------------------------------------------------------
    → (∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ g ; g′ ∣ ℓ ; ℓ′ ⊢ compile M ⊢M ⊑ compile M′ ⊢M′ ⇐ A ⊑ A′)
compile-pres-precision-app Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-app L⊑L′ M⊑M′)
  (⊢app {gc = gc} {gc′ = g₂} {A = A₁} {A₂} {B} {g = g₁} ⊢L ⊢M A₂≲A₁ g₁≾g₂ gc≾g₂)
  (⊢app {gc = gc′} {gc′ = g₂′} {A = A₁′} {A₂′} {B′} {g = g₁′} ⊢L′ ⊢M′ A₂′≲A₁′ g₁′≾g₂′ gc′≾g₂′) eq eq′
  with all-specific? [ gc , g₁ , g₂ ] | all-specific? [ gc′ , g₁′ , g₂′ ]
     | g₁≾g₂ | gc≾g₂ | g₁′≾g₂′ | gc′≾g₂′ | B | B′
... | yes (as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) (as-cons (＠ ℓ₃) as-nil)))
    | yes (as-cons (＠ ℓ₁′) (as-cons (＠ ℓ₂′) (as-cons (＠ ℓ₃′) as-nil)))
    | ≾-l ℓ₂≼ℓ₃ | ≾-l ℓ₁≼ℓ₃ | ≾-l ℓ₂′≼ℓ₃′ | ≾-l ℓ₁′≼ℓ₃′ | B | B′ =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case ⟨ gc⊑gc′ , cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ ⟩ of λ where
  ⟨ l⊑l , _ , _ , ⊑-ty l⊑l (⊑-fun l⊑l A₁⊑A₁′ B⊑B′) ⟩ →
    case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
    ⟨ _ , _ , A₂⊑A₂′ ⟩ →
      let sub : ⟦ l ℓ₃ ⟧ A₁ ⇒ B of l ℓ₂ <: ⟦ l (ℓ₁ ⋎ ℓ₂) ⟧ A₁ ⇒ B of l ℓ₂
          sub = <:-ty <:ₗ-refl (<:-fun (<:-l (ℓ₁⋎ℓ₂≼ℓ ℓ₁≼ℓ₃ ℓ₂≼ℓ₃)) <:-refl <:-refl) in
      let sub′ : ⟦ l ℓ₃′ ⟧ A₁′ ⇒ B′ of l ℓ₂′ <: ⟦ l (ℓ₁′ ⋎ ℓ₂′) ⟧ A₁′ ⇒ B′ of l ℓ₂′
          sub′ = <:-ty <:ₗ-refl (<:-fun (<:-l (ℓ₁⋎ℓ₂≼ℓ ℓ₁′≼ℓ₃′ ℓ₂′≼ℓ₃′)) <:-refl <:-refl) in
      ⊑-app (⊑-cast 𝒞L⊑𝒞L′ (coerce-prec (⊑-ty l⊑l (⊑-fun l⊑l A₁⊑A₁′ B⊑B′)) (⊑-ty l⊑l (⊑-fun l⊑l A₁⊑A₁′ B⊑B′)) (<:→≲ sub) (<:→≲ sub′)))
            (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec A₂⊑A₂′ A₁⊑A₁′ A₂≲A₁ A₂′≲A₁′)) refl refl
... | yes (as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) (as-cons (＠ ℓ₃) as-nil))) | no ¬as | _ | _ | _ | _ | _ | _ =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  case ⟨ gc⊑gc′ , cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ ⟩ of λ where
  ⟨ l⊑l {.ℓ₁} , _ , _ , ⊑-ty l⊑l (⊑-fun l⊑l A₁⊑A₁′ B⊑B′) ⟩ →
    let as = as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) (as-cons (＠ ℓ₃) as-nil)) in
    contradiction as ¬as
... | no _ | yes (as-cons (＠ ℓ₁′) (as-cons (＠ ℓ₂′) (as-cons (＠ ℓ₃′) as-nil))) | _ | _ | ≾-l ℓ₂′≼ℓ₃′ | ≾-l ℓ₁′≼ℓ₃′ | T of g₃ | B′ =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ of λ where
  ⟨ _ , _ , ⊑-ty g₁⊑g₁′ (⊑-fun g₂⊑g₂′ A₁⊑A₁′ (⊑-ty g₃⊑g₃′ T⊑T′)) ⟩ →
    let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
    let prec-src = ⊑-ty g₁⊑g₁′ (⊑-fun g₂⊑g₂′ A₁⊑A₁′ (⊑-ty g₃⊑g₃′ T⊑T′))
        prec-tgt = ⊑-ty ⋆⊑ (⊑-fun ⋆⊑ A₁⊑A₁′ (⊑-ty ⋆⊑ T⊑T′)) in
    let csub : ⟦ g₂ ⟧ A₁ ⇒ (T of g₃) of g₁ ≲ ⟦ ⋆ ⟧ A₁ ⇒ (T of ⋆) of ⋆
        csub = ≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl (≲-ty ≾-⋆r ≲ᵣ-refl)) in
    let sub : ⟦ l ℓ₃′ ⟧ A₁′ ⇒ B′ of l ℓ₂′ <: ⟦ l (ℓ₁′ ⋎ ℓ₂′) ⟧ A₁′ ⇒ B′ of l ℓ₂′
        sub = <:-ty <:ₗ-refl (<:-fun (<:-l (ℓ₁⋎ℓ₂≼ℓ ℓ₁′≼ℓ₃′ ℓ₂′≼ℓ₃′)) <:-refl <:-refl) in
    case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
    ⟨ _ , _ , A₂⊑A₂′ ⟩ →
      ⊑-castl (⊑-app⋆l (⊑-cast 𝒞L⊑𝒞L′ (coerce-prec prec-src prec-tgt csub (<:→≲ sub)))
                       (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec A₂⊑A₂′ A₁⊑A₁′ A₂≲A₁ A₂′≲A₁′)) refl)
              (coerce-prec-left (⊑-ty ⋆⊑ T⊑T′) (⊑-ty (consis-join-⊑ₗ g₃⊑g₃′ g₁⊑g₁′) T⊑T′) (≲-ty ≾-⋆l ≲ᵣ-refl))
... | no ¬as | no ¬as′ | _ | _ | _ | _ | T of g₃ | T′ of g₃′ =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ of λ where
  ⟨ _ , _ , ⊑-ty g₁⊑g₁′ (⊑-fun g₂⊑g₂′ A₁⊑A₁′ (⊑-ty g₃⊑g₃′ T⊑T′)) ⟩ →
    case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
    ⟨ _ , _ , A₂⊑A₂′ ⟩ →
      let prec-src = ⊑-ty g₁⊑g₁′ (⊑-fun g₂⊑g₂′ A₁⊑A₁′ (⊑-ty g₃⊑g₃′ T⊑T′))
          prec-tgt = ⊑-ty ⋆⊑ (⊑-fun ⋆⊑ A₁⊑A₁′ (⊑-ty ⋆⊑ T⊑T′)) in
      let csub : ⟦ g₂ ⟧ A₁ ⇒ (T of g₃) of g₁ ≲ ⟦ ⋆ ⟧ A₁ ⇒ (T of ⋆) of ⋆
          csub = ≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl (≲-ty ≾-⋆r ≲ᵣ-refl)) in
      let csub′ : ⟦ g₂′ ⟧ A₁′ ⇒ (T′ of g₃′) of g₁′ ≲ ⟦ ⋆ ⟧ A₁′ ⇒ (T′ of ⋆) of ⋆
          csub′ = ≲-ty ≾-⋆r (≲-fun ≾-⋆l ≲-refl (≲-ty ≾-⋆r ≲ᵣ-refl)) in
      ⊑-cast (⊑-app⋆ (⊑-cast 𝒞L⊑𝒞L′ (coerce-prec prec-src prec-tgt csub csub′)) (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec A₂⊑A₂′ A₁⊑A₁′ A₂≲A₁ A₂′≲A₁′)))
        (coerce-prec (⊑-ty ⋆⊑ T⊑T′) (⊑-ty (consis-join-⊑ₗ g₃⊑g₃′ g₁⊑g₁′) T⊑T′) _ _)


private
  compile-pres-precision-assign : ∀ {Γ Γ′ g g′ M M′ L L′ N N′ A A′} {p}
    → Γ ⊑* Γ′
    → g ⊑ₗ g′
    → ⊢ M ⊑ᴳ M′
    → (⊢M  : Γ  ; g  ⊢ᴳ M  ⦂ A )
    → (⊢M′ : Γ′ ; g′ ⊢ᴳ M′ ⦂ A′)
    → M  ≡ L  := N  at p
    → M′ ≡ L′ := N′ at p
      --------------------------------------------------------------------------------------------
    → (∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ g ; g′ ∣ ℓ ; ℓ′ ⊢ compile M ⊢M ⊑ compile M′ ⊢M′ ⇐ A ⊑ A′)
compile-pres-precision-assign Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-assign L⊑L′ M⊑M′)
    (⊢assign {gc = gc } {g = g } {ĝ } ⊢L  ⊢M  A≲Tĝ   g≾ĝ   gc≾ĝ  )
    (⊢assign {gc = gc′} {g = g′} {ĝ′} ⊢L′ ⊢M′ A′≲Tĝ′ g′≾ĝ′ gc′≾ĝ′) _ _
  with all-specific? [ gc , g , ĝ ] | all-specific? [ gc′ , g′ , ĝ′ ]
... | no _ | yes (as-cons (＠ ℓ₁)  (as-cons (＠ ℓ₂)  (as-cons (＠ ℓ₃) as-nil))) =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case ⟨ g′≾ĝ′ , gc′≾ĝ′ ⟩ of λ where
  ⟨ ≾-l g′≼ĝ′ , ≾-l gc′≼ĝ′ ⟩ →
    case   cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ of λ where
    ⟨ _ , _ , ⊑-ty g⊑g′ (⊑-ref B⊑B′) ⟩ →
      case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
      ⟨ _ , _ , A⊑A′ ⟩ →
        ⊑-assign?l (⊑-castl 𝒞L⊑𝒞L′ (inject-prec-left (⊑-ty g⊑g′ (⊑-ref B⊑B′))))
                   (⊑-cast  𝒞M⊑𝒞M′ (coerce-prec A⊑A′ B⊑B′ A≲Tĝ A′≲Tĝ′))
                   gc′≼ĝ′ g′≼ĝ′
... | yes (as-cons (＠ ℓ₁)  (as-cons (＠ ℓ₂)  (as-cons (＠ ℓ₃) as-nil))) | no ¬as =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  case ⟨ gc⊑gc′ , cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ ⟩ of λ where
  ⟨ l⊑l {.ℓ₁} , _ , _ , ⊑-ty (l⊑l {.ℓ₂}) (⊑-ref (⊑-ty (l⊑l {.ℓ₃}) T⊑T′)) ⟩ →
    let as = as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) (as-cons (＠ ℓ₃) as-nil)) in
    contradiction as ¬as
... | no _ | no _ =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
    case   cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ of λ where
    ⟨ _ , _ , ⊑-ty g⊑g′ (⊑-ref B⊑B′) ⟩ →
      case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
      ⟨ _ , _ , A⊑A′ ⟩ →
        ⊑-assign? (⊑-cast 𝒞L⊑𝒞L′ (inject-prec (⊑-ty g⊑g′ (⊑-ref B⊑B′))))
                  (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec A⊑A′ B⊑B′ A≲Tĝ A′≲Tĝ′))
... | yes (as-cons (＠ ℓ₁ )  (as-cons (＠ ℓ₂ )  (as-cons (＠ ℓ₃ ) as-nil)))
    | yes (as-cons (＠ ℓ₁′)  (as-cons (＠ ℓ₂′)  (as-cons (＠ ℓ₃′) as-nil)))
  with gc⊑gc′ | g≾ĝ     | gc≾ĝ
...  | l⊑l    | ≾-l g≼ĝ | ≾-l gc≼ĝ =
  let 𝒞L⊑𝒞L′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ L⊑L′ ⊢L ⊢L′ in
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case   cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞L⊑𝒞L′ of λ where
  ⟨ _ , _ , ⊑-ty l⊑l (⊑-ref (⊑-ty l⊑l T⊑T′)) ⟩ →
    case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
    ⟨ _ , _ , A⊑A′ ⟩ →
      ⊑-assign 𝒞L⊑𝒞L′ (⊑-cast 𝒞M⊑𝒞M′
                               (coerce-prec A⊑A′ (⊑-ty l⊑l T⊑T′) A≲Tĝ A′≲Tĝ′))
               gc≼ĝ g≼ĝ



{- Compiling values -}
compile-pres-precision Γ⊑Γ′ g⊑g′ ⊑ᴳ-const ⊢const ⊢const = ⊑-const
compile-pres-precision Γ⊑Γ′ g⊑g′ ⊑ᴳ-var (⊢var Γ∋x⦂A) (⊢var Γ′∋x⦂A′) = ⊑-var Γ∋x⦂A Γ′∋x⦂A′
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-lam g₁⊑g₂ A⊑A′ M⊑M′) (⊢lam ⊢M) (⊢lam ⊢M′) =
  ⊑-lam g₁⊑g₂ A⊑A′ (compile-pres-precision (⊑*-∷ A⊑A′ Γ⊑Γ′) g₁⊑g₂ M⊑M′ ⊢M ⊢M′)
{- Compiling function application -}
compile-pres-precision Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-app L⊑L′ N⊑N′) ⊢M ⊢M′ =
  compile-pres-precision-app Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-app L⊑L′ N⊑N′) ⊢M ⊢M′ refl refl
{- Compiling if-conditional -}
compile-pres-precision Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-if L⊑L′ N₁⊑N₁′ N₂⊑N₂′) ⊢M ⊢M′ =
  compile-pres-precision-if Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-if L⊑L′ N₁⊑N₁′ N₂⊑N₂′) ⊢M ⊢M′ refl refl
{- Compiling type annotation -}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-ann M⊑M′ A⊑A′) (⊢ann ⊢M B≲A) (⊢ann ⊢M′ B′≲A′) =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ g⊑g′ M⊑M′ ⊢M ⊢M′ in
  let ⟨ _ , _ , B⊑B′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ in
  ⊑-cast 𝒞M⊑𝒞M′ (coerce-prec B⊑B′ A⊑A′ B≲A B′≲A′)
{- Compiling let-expression -}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-let M⊑M′ N⊑N′) (⊢let ⊢M ⊢N) (⊢let ⊢M′ ⊢N′) =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ g⊑g′ M⊑M′ ⊢M ⊢M′ in
  let ⟨ _ , _ , A⊑A′ ⟩ = cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ in
  ⊑-let 𝒞M⊑𝒞M′ (compile-pres-precision (⊑*-∷ A⊑A′ Γ⊑Γ′) g⊑g′ N⊑N′ ⊢N ⊢N′)
{- Compiling reference creation -}
compile-pres-precision Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-ref M⊑M′) (⊢ref {gc = gc} ⊢M Tg≲Tℓ gc≾ℓ) (⊢ref {gc = gc′} ⊢M′ T′g′≲T′ℓ gc′≾ℓ) with gc | gc′ | gc⊑gc′
... | l ℓc | l .ℓc | l⊑l =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ l⊑l M⊑M′ ⊢M ⊢M′ in
  case ⟨ gc′≾ℓ , cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ ⟩ of λ where
  ⟨ ≾-l ℓc≼ℓ , _ , _ , ⊑-ty g⊑g′ T⊑T′ ⟩ →
    ⊑-ref (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec (⊑-ty g⊑g′ T⊑T′) (⊑-ty l⊑l T⊑T′) Tg≲Tℓ T′g′≲T′ℓ)) ℓc≼ℓ
... | ⋆ | ⋆ | ⋆⊑ =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
  ⟨ _ , _ , ⊑-ty g⊑g′ T⊑T′ ⟩ →
    ⊑-ref? (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec (⊑-ty g⊑g′ T⊑T′) (⊑-ty l⊑l T⊑T′) Tg≲Tℓ T′g′≲T′ℓ))
... | ⋆ | l ℓc′ | ⋆⊑ =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ ⋆⊑ M⊑M′ ⊢M ⊢M′ in
  case ⟨ gc′≾ℓ , cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ ⟩ of λ where
  ⟨ ≾-l ℓc′≼ℓ , _ , _ , ⊑-ty g⊑g′ T⊑T′ ⟩ →
    ⊑-ref?l (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec (⊑-ty g⊑g′ T⊑T′) (⊑-ty l⊑l T⊑T′) Tg≲Tℓ T′g′≲T′ℓ)) ℓc′≼ℓ
... | l ℓc | ⋆ | ()
{- Compiling dereference -}
compile-pres-precision Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-deref M⊑M′) (⊢deref {A = A} {g} ⊢M) (⊢deref {A = A′} {g′} ⊢M′)
  with g | g′ | A | A′
... | l ℓ | l ℓ′ | _ | _ =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
  ⟨ _ , _ , ⊑-ty l⊑l _ ⟩ → ⊑-deref 𝒞M⊑𝒞M′ refl refl
... | ⋆ | ⋆ | T of g₁ | T′ of g₁′ rewrite g⋎̃⋆≡⋆ {g₁} | g⋎̃⋆≡⋆ {g₁′} =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
  ⟨ _ , _ , ⊑-ty g⊑g′ (⊑-ref (⊑-ty g₁⊑g₁′ T⊑T′)) ⟩ →
    ⊑-deref⋆ (⊑-cast 𝒞M⊑𝒞M′ (coerce-prec (⊑-ty ⋆⊑ (⊑-ref (⊑-ty g₁⊑g₁′ T⊑T′)))
                             (⊑-ty ⋆⊑ (⊑-ref (⊑-ty ⋆⊑ T⊑T′)))
                             (≲-ty ≾-⋆l (≲-ref (≲-ty ≾-⋆r ≲ᵣ-refl) (≲-ty ≾-⋆l ≲ᵣ-refl)))
                             (≲-ty ≾-⋆l (≲-ref (≲-ty ≾-⋆r ≲ᵣ-refl) (≲-ty ≾-⋆l ≲ᵣ-refl)))))
... | ⋆ | l ℓ′ | T of g₁ | A′ rewrite g⋎̃⋆≡⋆ {g₁} =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
  ⟨ _ , _ , ⊑-ty g⊑g′ (⊑-ref (⊑-ty g₁⊑g₁′ T⊑T′)) ⟩ →
    ⊑-deref⋆l (⊑-castl 𝒞M⊑𝒞M′ (coerce-prec-left (⊑-ty ⋆⊑ (⊑-ref (⊑-ty g₁⊑g₁′ T⊑T′)))
                            (⊑-ty ⋆⊑ (⊑-ref (⊑-ty ⋆⊑ T⊑T′)))
                            (≲-ty ≾-⋆l (≲-ref (≲-ty ≾-⋆r ≲ᵣ-refl) (≲-ty ≾-⋆l ≲ᵣ-refl))))) refl
... | l ℓ | ⋆ | _ | _ =
  let 𝒞M⊑𝒞M′ = compile-pres-precision Γ⊑Γ′ gc⊑gc′ M⊑M′ ⊢M ⊢M′ in
  case cc-prec-inv {ℓv = low} {low} Γ⊑Γ′ ⟨ ⊑-∅ , ⊑-∅ ⟩ 𝒞M⊑𝒞M′ of λ where
  ⟨ _ , _ , ⊑-ty () _ ⟩
{- Compiling reference assignment -}
compile-pres-precision Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-assign L⊑L′ M⊑M′) ⊢M ⊢M′ =
  compile-pres-precision-assign Γ⊑Γ′ gc⊑gc′ (⊑ᴳ-assign L⊑L′ M⊑M′) ⊢M ⊢M′ refl refl
