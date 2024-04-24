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


{- Here is the (lemma?) statement of "compilation preserves precision" -}
compile-pres-precision : ∀ {Γ Γ′ g g′ M M′ A A′}
  → Γ ⊑* Γ′
  → g ⊑ₗ g′
  → ⊢ M ⊑ᴳ M′
  → (⊢M  : Γ  ; g  ⊢ᴳ M  ⦂ A )
  → (⊢M′ : Γ′ ; g′ ⊢ᴳ M′ ⦂ A′)
    --------------------------------------------------------------------------------------------
  → (∀ {ℓ ℓ′} → Γ ; Γ′ ∣ ∅ ; ∅ ∣ g ; g′ ∣ ℓ ; ℓ′ ⊢ compile M ⊢M ⊑ compile M′ ⊢M′ ⇐ A ⊑ A′)


{- There are quite a few cases about compiling an if-conditional,
   so let's put them in a separate lemma. -}
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
  with all-specific-dec [ gc , g ] | all-specific-dec [ gc′ , g′ ]
... | yes (as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) as-nil))
    | yes (as-cons (＠ ℓ₁′) (as-cons (＠ ℓ₂′) as-nil)) = {!!}
... | yes (as-cons (＠ ℓ₁) (as-cons (＠ ℓ₂) as-nil)) | no _ = {!!}
... | no _ | yes (as-cons (＠ ℓ₁′) (as-cons (＠ ℓ₂′) as-nil)) = {!!}
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
  with all-specific-dec [ gc , g , ĝ ] | all-specific-dec [ gc′ , g′ , ĝ′ ]
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
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-app M⊑M′ M⊑M′₁) ⊢M ⊢M′ = {!!}
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
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-ref M⊑M′) ⊢M ⊢M′ = {!!}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-deref M⊑M′) ⊢M ⊢M′ = {!!}
compile-pres-precision Γ⊑Γ′ g⊑g′ (⊑ᴳ-assign L⊑L′ M⊑M′)
                       (⊢assign {gc = gc } {g = g } {ĝ } ⊢L ⊢M A≲Tĝ g≾ĝ gc≾ĝ)
                       (⊢assign {gc = gc′} {g = g′} {ĝ′} ⊢L′ ⊢M′ A′≲Tĝ′ g′≾ĝ′ gc′≾ĝ′) = {!!}
