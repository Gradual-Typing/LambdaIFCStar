{- Precision relation of CC2 -}

open import Common.Types

module CC2.Precision where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax hiding (_⨟_)
open import Common.Utils
open import CC2.Statics
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)
open import Memory.HeapContext
open import CoercionExpr.Precision
  renaming (prec→⊑ to cexpr-prec→⊑;
            ⊢l_⊑_ to ⊢ₗ_⊑_; ⊢r_⊑_ to ⊢ᵣ_⊑_)
open import CoercionExpr.SyntacComp renaming (_⨟_ to _⊹⊹_)


data _⊑*_ : (Γ Γ′ : Context) → Set where

  ⊑*-∅ : [] ⊑* []

  ⊑*-∷ : ∀ {Γ Γ′ A A′} → A ⊑ A′ → Γ ⊑* Γ′ → (A ∷ Γ) ⊑* (A′ ∷ Γ′)


⊑*→⊑ : ∀ {Γ Γ′ A A′ x} → Γ ⊑* Γ′ → Γ ∋ x ⦂ A → Γ′ ∋ x ⦂ A′ → A ⊑ A′
⊑*→⊑ {x = 0}     (⊑*-∷ A⊑A′ Γ⊑Γ′) refl refl = A⊑A′
⊑*→⊑ {x = suc x} (⊑*-∷ A⊑A′ Γ⊑Γ′) Γ∋x  Γ′∋x = ⊑*→⊑ Γ⊑Γ′ Γ∋x Γ′∋x


data _⊑ₕ_ : (Σ Σ′ : HalfHeapContext) → Set where

  ⊑-∅ : [] ⊑ₕ []

  ⊑-∷ : ∀ {Σ Σ′ T T′ n} → T ⊑ᵣ T′ → Σ ⊑ₕ Σ′ → (⟨ n , T ⟩ ∷ Σ) ⊑ₕ (⟨ n , T′ ⟩ ∷ Σ′)

_⊑ₘ_ : (Σ Σ′ : HeapContext) → Set
⟨ Σᴸ , Σᴴ ⟩ ⊑ₘ ⟨ Σᴸ′ , Σᴴ′ ⟩ = (Σᴸ ⊑ₕ Σᴸ′) × (Σᴴ ⊑ₕ Σᴴ′)

⊑ₕ→⊑ : ∀ {Σ Σ′ T T′ n}
  → Σ ⊑ₕ Σ′
  → find _≟_ Σ  n ≡ just T
  → find _≟_ Σ′ n ≡ just T′
  → T ⊑ᵣ T′
⊑ₕ→⊑ {⟨ n₀ , T ⟩ ∷ _} {⟨ n₀ , T′ ⟩ ∷ _} {n = n} (⊑-∷ T⊑T′ Σ⊑Σ′) eq eq′
  with n ≟ n₀
... | no _ = ⊑ₕ→⊑ Σ⊑Σ′ eq eq′
... | yes refl with eq | eq′
... | refl | refl = T⊑T′

⊑ₘ→⊑ : ∀ {Σ Σ′ T T′ n ℓ̂}
  → Σ ⊑ₘ Σ′
  → let a = a⟦ ℓ̂ ⟧ n in
     lookup-Σ Σ  a ≡ just T
  → lookup-Σ Σ′ a ≡ just T′
  → T ⊑ᵣ T′
⊑ₘ→⊑ {ℓ̂ = low}  ⟨ Σᴸ⊑ , _ ⟩ Σa≡T Σ′a≡T′ = ⊑ₕ→⊑ Σᴸ⊑ Σa≡T Σ′a≡T′
⊑ₘ→⊑ {ℓ̂ = high} ⟨ _ , Σᴴ⊑ ⟩ Σa≡T Σ′a≡T′ = ⊑ₕ→⊑ Σᴴ⊑ Σa≡T Σ′a≡T′


infix 4 ⟨_⟩⊑⟨_⟩
infix 4 ⟨_⟩⊑_
infix 4 _⊑⟨_⟩

data ⟨_⟩⊑⟨_⟩ : ∀ {A A′ B B′} → Cast A ⇒ B → Cast A′ ⇒ B′ → Set where

  ⊑-base : ∀ {ι g₁ g₁′ g₂ g₂′} {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ c̅ ⊑ c̅′
      --------------------------------------------------------
    → ⟨ cast (Castᵣ_⇒_.id ι) c̅ ⟩⊑⟨ cast (Castᵣ_⇒_.id ι) c̅′ ⟩

  ⊑-ref : ∀ {A A′ B B′ g₁ g₁′ g₂ g₂′} {c : Cast B ⇒ A} {c′ : Cast B′ ⇒ A′}
            {d : Cast A ⇒ B} {d′ : Cast A′ ⇒ B′}
            {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⟨ c ⟩⊑⟨ c′ ⟩
    → ⟨ d ⟩⊑⟨ d′ ⟩
    → ⊢ c̅ ⊑ c̅′
      --------------------------------------------------------
    → ⟨ cast (ref c d) c̅ ⟩⊑⟨ cast (ref c′ d′) c̅′ ⟩

  ⊑-fun : ∀ {A A′ B B′ C C′ D D′ gc₁ gc₁′ gc₂ gc₂′ g₁ g₁′ g₂ g₂′}
            {c : Cast C ⇒ A} {c′ : Cast C′ ⇒ A′}
            {d : Cast B ⇒ D} {d′ : Cast B′ ⇒ D′}
            {d̅ : CExpr gc₂ ⇒ gc₁} {d̅′ : CExpr gc₂′ ⇒ gc₁′}
            {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ d̅ ⊑ d̅′
    → ⟨ c ⟩⊑⟨ c′ ⟩
    → ⟨ d ⟩⊑⟨ d′ ⟩
    → ⊢ c̅ ⊑ c̅′
      --------------------------------------------------------
    → ⟨ cast (fun d̅ c d) c̅ ⟩⊑⟨ cast (fun d̅′ c′ d′) c̅′ ⟩


data ⟨_⟩⊑_ : ∀ {A B} → Cast A ⇒ B → (A′ : Type) → Set where

  ⊑-base : ∀ {ι g₁ g₂ g′} {c̅ : CExpr g₁ ⇒ g₂}
    → ⊢ₗ c̅ ⊑ g′
      --------------------------------------------------------
    → ⟨ cast (Castᵣ_⇒_.id ι) c̅ ⟩⊑ ` ι of g′

  ⊑-ref : ∀ {A A′ B g₁ g₂ g′} {c : Cast B ⇒ A} {d : Cast A ⇒ B}
            {c̅ : CExpr g₁ ⇒ g₂}
    → ⟨ c ⟩⊑ A′
    → ⟨ d ⟩⊑  A′
    → ⊢ₗ c̅ ⊑ g′
      --------------------------------------------------------
    → ⟨ cast (ref c d) c̅ ⟩⊑ Ref A′ of g′

  ⊑-fun : ∀ {A A′ B B′ C D gc₁ gc₂ gc′ g₁ g₂ g′}
            {c : Cast C ⇒ A} {d : Cast B ⇒ D}
            {d̅ : CExpr gc₂ ⇒ gc₁} {c̅ : CExpr g₁ ⇒ g₂}
    → ⊢ₗ d̅ ⊑ gc′
    → ⟨ c ⟩⊑ A′
    → ⟨ d ⟩⊑ B′
    → ⊢ₗ c̅ ⊑ g′
      --------------------------------------------------------
    → ⟨ cast (fun d̅ c d) c̅ ⟩⊑ ⟦ gc′ ⟧ A′ ⇒ B′ of g′


data _⊑⟨_⟩ : ∀ {A′ B′} → (A : Type) → Cast A′ ⇒ B′ → Set where

  ⊑-base : ∀ {ι g g₁′ g₂′} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ᵣ g ⊑ c̅′
      --------------------------------------------------------
    → ` ι of g ⊑⟨ cast (Castᵣ_⇒_.id ι) c̅′ ⟩

  ⊑-ref : ∀ {A A′ B′ g g₁′ g₂′} {c′ : Cast B′ ⇒ A′} {d′ : Cast A′ ⇒ B′}
            {c̅′ : CExpr g₁′ ⇒ g₂′}
    → A ⊑⟨ c′ ⟩
    → A ⊑⟨ d′ ⟩
    → ⊢ᵣ g ⊑ c̅′
      --------------------------------------------------------
    → Ref A of g ⊑⟨ cast (ref c′ d′) c̅′ ⟩

  ⊑-fun : ∀ {A A′ B B′ C′ D′ gc gc₁′ gc₂′ g g₁′ g₂′}
            {c′ : Cast C′ ⇒ A′} {d′ : Cast B′ ⇒ D′}
            {d̅′ : CExpr gc₂′ ⇒ gc₁′} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ᵣ gc ⊑ d̅′
    → A ⊑⟨ c′ ⟩
    → B ⊑⟨ d′ ⟩
    → ⊢ᵣ g ⊑ c̅′
      --------------------------------------------------------
    → ⟦ gc ⟧ A ⇒ B of g ⊑⟨ cast (fun d̅′ c′ d′) c̅′ ⟩


coercion-prec→⊑ : ∀ {A A′ B B′} {c : Cast A ⇒ B} {d : Cast A′ ⇒ B′}
  → ⟨ c ⟩⊑⟨ d ⟩
  → A ⊑ A′ × B ⊑ B′
coercion-prec→⊑ (⊑-base c̅⊑c̅′) =
  let ⟨ g₁⊑g₁′ , g₂⊑g₂′ ⟩ = cexpr-prec→⊑ _ _ c̅⊑c̅′ in
  ⟨ ⊑-ty g₁⊑g₁′ ⊑-ι , ⊑-ty g₂⊑g₂′ ⊑-ι ⟩
coercion-prec→⊑ (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) =
  let ⟨ g₁⊑g₁′ , g₂⊑g₂′ ⟩ = cexpr-prec→⊑ _ _ c̅⊑c̅′ in
  let ⟨ B⊑B′ , A⊑A′ ⟩ = coercion-prec→⊑ c⊑c′ in
  ⟨ ⊑-ty g₁⊑g₁′ (⊑-ref A⊑A′) , ⊑-ty g₂⊑g₂′ (⊑-ref B⊑B′) ⟩
coercion-prec→⊑ (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′) =
  let ⟨ g₁⊑g₁′   , g₂⊑g₂′   ⟩ = cexpr-prec→⊑ _ _ c̅⊑c̅′ in
  let ⟨ gc₂⊑gc₂′ , gc₁⊑gc₁′ ⟩ = cexpr-prec→⊑ _ _ d̅⊑d̅′ in
  let ⟨ C⊑C′ , A⊑A′ ⟩ = coercion-prec→⊑ c⊑c′ in
  let ⟨ B⊑B′ , D⊑D′ ⟩ = coercion-prec→⊑ d⊑d′ in
  ⟨ ⊑-ty g₁⊑g₁′ (⊑-fun gc₁⊑gc₁′ A⊑A′ B⊑B′) , ⊑-ty g₂⊑g₂′ (⊑-fun gc₂⊑gc₂′ C⊑C′ D⊑D′) ⟩

coercion-prec-left→⊑ : ∀ {A A′ B} {c : Cast A ⇒ B}
  → ⟨ c ⟩⊑ A′
  → A ⊑ A′ × B ⊑ A′
coercion-prec-left→⊑ (⊑-base c̅⊑g′) =
  let ⟨ g₁⊑g′ , g₂⊑g′ ⟩ = prec-left→⊑ _ c̅⊑g′ in
  ⟨ ⊑-ty g₁⊑g′ ⊑-ι , ⊑-ty g₂⊑g′ ⊑-ι ⟩
coercion-prec-left→⊑ (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  let ⟨ g₁⊑g′ , g₂⊑g′ ⟩ = prec-left→⊑ _ c̅⊑g′ in
  let ⟨ B⊑A′ , A⊑A′ ⟩ = coercion-prec-left→⊑ c⊑A′ in
  ⟨ ⊑-ty g₁⊑g′ (⊑-ref A⊑A′) , ⊑-ty g₂⊑g′ (⊑-ref B⊑A′) ⟩
coercion-prec-left→⊑ (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) =
  let ⟨ g₁⊑g′   , g₂⊑g′   ⟩ = prec-left→⊑ _ c̅⊑g′ in
  let ⟨ gc₂⊑gc′ , gc₁⊑gc′ ⟩ = prec-left→⊑ _ d̅⊑gc′ in
  let ⟨ C⊑A′ , A⊑A′ ⟩ = coercion-prec-left→⊑ c⊑A′ in
  let ⟨ B⊑B′ , D⊑B′ ⟩ = coercion-prec-left→⊑ d⊑B′ in
  ⟨ ⊑-ty g₁⊑g′ (⊑-fun gc₁⊑gc′ A⊑A′ B⊑B′) , ⊑-ty g₂⊑g′ (⊑-fun gc₂⊑gc′ C⊑A′ D⊑B′) ⟩

coercion-prec-right→⊑ : ∀ {A A′ B′} {c : Cast A′ ⇒ B′}
  → A ⊑⟨ c ⟩
  → A ⊑ A′ × A ⊑ B′
coercion-prec-right→⊑ (⊑-base g⊑c̅′) =
  let ⟨ g⊑g₁′ , g⊑g₂′ ⟩ = prec-right→⊑ _ g⊑c̅′ in
  ⟨ ⊑-ty g⊑g₁′ ⊑-ι , ⊑-ty g⊑g₂′ ⊑-ι ⟩
coercion-prec-right→⊑ (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) =
  let ⟨ g⊑g₁′ , g⊑g₂′ ⟩ = prec-right→⊑ _ g⊑c̅′ in
  let ⟨ A⊑B′ , A⊑A′ ⟩ = coercion-prec-right→⊑ A⊑c′ in
  ⟨ ⊑-ty g⊑g₁′ (⊑-ref A⊑A′) , ⊑-ty g⊑g₂′ (⊑-ref A⊑B′) ⟩
coercion-prec-right→⊑ (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′) =
  let ⟨ g⊑g₁′   , g⊑g₂′   ⟩ = prec-right→⊑ _ g⊑c̅′ in
  let ⟨ gc⊑gc₂′ , gc⊑gc₁′ ⟩ = prec-right→⊑ _ gc⊑d̅′ in
  let ⟨ A⊑C′ , A⊑A′ ⟩ = coercion-prec-right→⊑ A⊑c′ in
  let ⟨ B⊑B′ , B⊑D′ ⟩ = coercion-prec-right→⊑ B⊑d′ in
  ⟨ ⊑-ty g⊑g₁′ (⊑-fun gc⊑gc₁′ A⊑A′ B⊑B′) , ⊑-ty g⊑g₂′ (⊑-fun gc⊑gc₂′ A⊑C′ B⊑D′) ⟩


-- comp-pres-prec-ll : ∀ {A A′ B C} {c : Cast A ⇒ B} {d : Cast B ⇒ C}
--   → ⟨     c ⟩⊑ A′
--   → ⟨     d ⟩⊑ A′
--     -----------------------
--   → ⟨ c ⨟ d ⟩⊑ A′
-- comp-pres-prec-ll (⊑-base c̅⊑g′) (⊑-base d̅⊑g′) = ⊑-base (comp-pres-⊑-ll c̅⊑g′ d̅⊑g′)
-- comp-pres-prec-ll (⊑-ref c₁⊑A′ d₁⊑A′ c̅⊑g′) (⊑-ref c₂⊑A′ d₂⊑A′ d̅⊑g′) =
--   ⊑-ref (comp-pres-prec-ll c₂⊑A′ c₁⊑A′) (comp-pres-prec-ll d₁⊑A′ d₂⊑A′)
--         (comp-pres-⊑-ll c̅⊑g′ d̅⊑g′)
-- comp-pres-prec-ll (⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′) (⊑-fun d̅₂⊑gc′ c₂⊑A′ d₂⊑B′ c̅₂⊑g′) =
--   ⊑-fun (comp-pres-⊑-ll d̅₂⊑gc′ d̅₁⊑gc′) (comp-pres-prec-ll c₂⊑A′ c₁⊑A′)
--         (comp-pres-prec-ll d₁⊑B′ d₂⊑B′) (comp-pres-⊑-ll c̅₁⊑g′ c̅₂⊑g′)


infix 4 _;_∣_;_∣_;_∣_;_⊢_⊑_⇐_⊑_

data _;_∣_;_∣_;_∣_;_⊢_⊑_⇐_⊑_ : (Γ Γ′ : Context) (Σ Σ′ : HeapContext)
  (g g′ : Label) (ℓ ℓ′ : StaticLabel) (M M′ : Term) (A A′ : Type) → Set where

  ⊑-var : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ A A′ x}
    → Γ  ∋ x ⦂ A
    → Γ′ ∋ x ⦂ A′
      ---------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ` x ⊑ ` x ⇐ A ⊑ A′


  ⊑-const : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′ ι ℓ} {k : rep ι}
      ---------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ $ k ⊑ $ k
         ⇐ ` ι of l ℓ ⊑ ` ι of l ℓ


  ⊑-addr : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {n ℓ ℓ̂ T T′}
    → lookup-Σ Σ  (a⟦ ℓ̂ ⟧ n) ≡ just T
    → lookup-Σ Σ′ (a⟦ ℓ̂ ⟧ n) ≡ just T′
      -------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ addr n ⊑ addr n
         ⇐ Ref (T of l ℓ̂) of l ℓ ⊑ Ref (T′ of l ℓ̂) of l ℓ


  ⊑-lam : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {N N′} {g g′ A A′ B B′ ℓ}
    → g ⊑ₗ g′
    → A ⊑  A′
    → (∀ {ℓv ℓv′} → A ∷ Γ ; A′ ∷ Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ B ⊑ B′)
      --------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ƛ N ⊑ ƛ N′
         ⇐ ⟦ g ⟧ A ⇒ B of l ℓ ⊑ ⟦ g′ ⟧ A′ ⇒ B′ of l ℓ


  ⊑-app : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {L L′ M M′} {A A′ B B′ C C′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ⟦ l (ℓc ⋎ ℓ) ⟧ A ⇒ B of l ℓ ⊑ ⟦ l (ℓc ⋎ ℓ) ⟧ A′ ⇒ B′ of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → C  ≡ stamp B  (l ℓ)
    → C′ ≡ stamp B′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ app L M A B ℓ ⊑ app L′ M′ A′ B′ ℓ ⇐ C ⊑ C′


  ⊑-app! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {L L′ M M′} {A A′ B B′ C C′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ⟦ ⋆ ⟧ A ⇒ B of ⋆ ⊑ ⟦ ⋆ ⟧ A′ ⇒ B′ of ⋆
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → C  ≡ stamp B  ⋆
    → C′ ≡ stamp B′ ⋆
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ app! L M A B ⊑ app! L′ M′ A′ B′ ⇐ C ⊑ C′


  ⊑-app!l : ∀ {Γ Γ′ Σ Σ′ gc ℓc ℓv ℓv′} {L L′ M M′} {A A′ B B′ C C′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ⟦ ⋆ ⟧ A ⇒ B of ⋆ ⊑ ⟦ l (ℓc ⋎ ℓ) ⟧ A′ ⇒ B′ of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → C  ≡ stamp B     ⋆
    → C′ ≡ stamp B′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ app! L M A B ⊑ app L′ M′ A′ B′ ℓ ⇐ C ⊑ C′


  ⊑-if : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {L L′ M M′ N N′} {A A′ B B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ` Bool of l ℓ ⊑ ` Bool of l ℓ
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l (ℓc ⋎ ℓ) ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ A ⊑ A′)
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l (ℓc ⋎ ℓ) ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ A ⊑ A′)
    → B  ≡ stamp A  (l ℓ)
    → B′ ≡ stamp A′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ if L A ℓ M N ⊑ if L′ A′ ℓ M′ N′ ⇐ B ⊑ B′


  ⊑-if! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {L L′ M M′ N N′} {A A′ B B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ` Bool of ⋆ ⊑ ` Bool of ⋆
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ A ⊑ A′)
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ A ⊑ A′)
    → B  ≡ stamp A  ⋆
    → B′ ≡ stamp A′ ⋆
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ if! L A M N ⊑ if! L′ A′ M′ N′ ⇐ B ⊑ B′


  ⊑-if!l : ∀ {Γ Γ′ Σ Σ′ gc ℓc ℓv ℓv′} {L L′ M M′ N N′} {A A′ B B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ ` Bool of ⋆ ⊑ ` Bool of l ℓ
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ A ⊑ A′)
    → (∀ {ℓv ℓv′} → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l (ℓc ⋎ ℓ) ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ A ⊑ A′)
    → B  ≡ stamp A  ⋆
    → B′ ≡ stamp A′ (l ℓ)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ if! L A M N ⊑ if L′ A′ ℓ M′ N′ ⇐ B ⊑ B′


  ⊑-let : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′ N N′} {A A′ B B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ A ⊑ A′
    → (∀ {ℓv ℓv′} → A ∷ Γ ; A′ ∷ Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′
         ⇐ B ⊑ B′)
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ `let M A N ⊑ `let M′ A′ N′ ⇐ B ⊑ B′


  ⊑-ref : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {M M′} {T T′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ T of l ℓ ⊑ T′ of l ℓ
    → ℓc ≼ ℓ
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ ref⟦ ℓ ⟧ M ⊑ ref⟦ ℓ ⟧ M′
         ⇐ Ref (T of l ℓ) of l low ⊑ Ref (T′ of l ℓ) of l low


  ⊑-ref? : ∀ {Γ Γ′ Σ Σ′ ℓv ℓv′} {M M′} {T T′ ℓ} {p q}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ T of l ℓ ⊑ T′ of l ℓ
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; ⋆ ∣ ℓv ; ℓv′ ⊢ ref?⟦ ℓ ⟧ M p ⊑ ref?⟦ ℓ ⟧ M′ q
         ⇐ Ref (T of l ℓ) of l low ⊑ Ref (T′ of l ℓ) of l low


  ⊑-ref?l : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {M M′} {T T′ ℓ} {p}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ T of l ℓ ⊑ T′ of l ℓ
    → ℓc ≼ ℓ
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ ⋆ ; l ℓc ∣ ℓv ; ℓv′ ⊢ ref?⟦ ℓ ⟧ M p ⊑ ref⟦ ℓ ⟧ M′
         ⇐ Ref (T of l ℓ) of l low ⊑ Ref (T′ of l ℓ) of l low


  ⊑-deref : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ Ref A of l ℓ ⊑ Ref A′ of l ℓ
    → B  ≡ stamp A  (l ℓ)
    → B′ ≡ stamp A′ (l ℓ)
      ----------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ ! M A ℓ ⊑ ! M′ A′ ℓ ⇐ B ⊑ B′


  ⊑-deref! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ Ref A of ⋆ ⊑ Ref A′ of ⋆
    → B  ≡ stamp A  ⋆
    → B′ ≡ stamp A′ ⋆
      ----------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ !! M A ⊑ !! M′ A′ ⇐ B ⊑ B′


  ⊑-deref!l : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B B′ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ Ref A of ⋆ ⊑ Ref A′ of l ℓ
    → B  ≡ stamp A  ⋆
    → B′ ≡ stamp A′ (l ℓ)
      ----------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ !! M A ⊑ ! M′ A′ ℓ ⇐ B ⊑ B′


  ⊑-assign : ∀ {Γ Γ′ Σ Σ′ ℓc ℓv ℓv′} {L L′ M M′} {T T′ ℓ̂ ℓ}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ Ref (T of l ℓ̂) of l ℓ ⊑ Ref (T′ of l ℓ̂) of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of l ℓ̂ ⊑ T′ of l ℓ̂
    → ℓc ≼ ℓ̂ → ℓ ≼ ℓ̂
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ l ℓc ; l ℓc ∣ ℓv ; ℓv′ ⊢ assign L M T ℓ̂ ℓ ⊑ assign L′ M′ T′ ℓ̂ ℓ
         ⇐ ` Unit of l low ⊑ ` Unit of l low


  ⊑-assign? : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {L L′ M M′} {T T′ ĝ ĝ′ g g′} {p q}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ Ref (T of ĝ) of g ⊑ Ref (T′ of ĝ′) of g′
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of ĝ ⊑ T′ of ĝ′
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ assign? L M T ĝ g p ⊑ assign? L′ M′ T′ ĝ′ g′ q
         ⇐ ` Unit of l low ⊑ ` Unit of l low


  ⊑-assign?l : ∀ {Γ Γ′ Σ Σ′ gc ℓc ℓv ℓv′} {L L′ M M′} {T T′ ĝ ℓ̂ g ℓ} {p}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ L ⊑ L′
         ⇐ Ref (T of ĝ) of g ⊑ Ref (T′ of l ℓ̂) of l ℓ
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ M ⊑ M′
         ⇐ T of ĝ ⊑ T′ of l ℓ̂
    → ℓc ≼ ℓ̂ → ℓ ≼ ℓ̂
      -------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; l ℓc ∣ ℓv ; ℓv′ ⊢ assign? L M T ĝ g p ⊑ assign L′ M′ T′ ℓ̂ ℓ
         ⇐ ` Unit of l low ⊑ ` Unit of l low


  ⊑-prot : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv₁ ℓv₁′} {M M′ PC PC′} {A A′ B B′ g g′ ℓ} {vc vc′}
    → let ℓv₂  = ∥ PC  ∥ vc  in
       let ℓv₂′ = ∥ PC′ ∥ vc′ in
       Γ ; Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv₂ ; ℓv₂′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → PC ⊑ PC′ ⇐ g ⊑ g′
    → ℓv₁  ⋎ ℓ  ≼ ℓv₂
    → ℓv₁′ ⋎ ℓ ≼ ℓv₂′
    → B  ≡ stamp A  (l ℓ)
    → B′ ≡ stamp A′ (l ℓ)
      ----------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv₁ ; ℓv₁′ ⊢ prot PC vc ℓ M A ⊑ prot PC′ vc′ ℓ M′ A′ ⇐ B ⊑ B′


  ⊑-prot! : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv₁ ℓv₁′} {M M′ PC PC′} {A A′ B B′ g g′ ℓ ℓ′} {vc vc′}
    → let ℓv₂  = ∥ PC  ∥ vc  in
       let ℓv₂′ = ∥ PC′ ∥ vc′ in
       Γ ; Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv₂ ; ℓv₂′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → PC ⊑ PC′ ⇐ g ⊑ g′
    → ℓv₁  ⋎ ℓ  ≼ ℓv₂
    → ℓv₁′ ⋎ ℓ′ ≼ ℓv₂′
    → B  ≡ stamp A  ⋆
    → B′ ≡ stamp A′ ⋆
    → ℓ ≼ ℓ′
      ----------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv₁ ; ℓv₁′ ⊢ prot! PC vc ℓ M A ⊑ prot! PC′ vc′ ℓ′ M′ A′ ⇐ B ⊑ B′


  ⊑-prot!l : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv₁ ℓv₁′} {M M′ PC PC′} {A A′ B B′ g g′ ℓ ℓ′} {vc vc′}
    → let ℓv₂  = ∥ PC  ∥ vc  in
       let ℓv₂′ = ∥ PC′ ∥ vc′ in
       Γ ; Γ′ ∣ Σ ; Σ′ ∣ g ; g′ ∣ ℓv₂ ; ℓv₂′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → PC ⊑ PC′ ⇐ g ⊑ g′
    → ℓv₁  ⋎ ℓ  ≼ ℓv₂
    → ℓv₁′ ⋎ ℓ′ ≼ ℓv₂′
    → B  ≡ stamp A  ⋆
    → B′ ≡ stamp A′ (l ℓ′)
    → ℓ ≼ ℓ′
      ----------------------------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv₁ ; ℓv₁′ ⊢ prot! PC vc ℓ M A ⊑ prot PC′ vc′ ℓ′ M′ A′ ⇐ B ⊑ B′


  ⊑-cast : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B B′}
             {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → ⟨ c ⟩⊑⟨ c′ ⟩
      -------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⇐ B ⊑ B′


  ⊑-castl : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B} {c : Cast A ⇒ B}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → ⟨ c ⟩⊑ A′
      -------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⟨ c ⟩ ⊑ M′ ⇐ B ⊑ A′


  ⊑-castr : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′ B′} {c′ : Cast A′ ⇒ B′}
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    → A ⊑⟨ c′ ⟩
      -------------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⟨ c′ ⟩ ⇐ A ⊑ B′


  ⊑-blame : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M A A′ p}
    → Γ ; Σ ; gc ; ℓv ⊢ M ⇐ A
    → A ⊑ A′
      ------------------------------------------------------------------
    → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ blame p ⇐ A ⊑ A′


{- The term precision relation implies that both terms are well-typed.
   Furthermore, their types are related by type precision. -}
cc-prec-inv : ∀ {Γ Γ′ Σ Σ′ gc gc′ ℓv ℓv′} {M M′} {A A′}
  → Γ ⊑* Γ′
  → Σ ⊑ₘ Σ′
  → Γ ; Γ′ ∣ Σ ; Σ′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
    -------------------------------------------------------------
  → Γ  ; Σ  ; gc  ; ℓv  ⊢ M  ⇐ A    ×
     Γ′ ; Σ′ ; gc′ ; ℓv′ ⊢ M′ ⇐ A′   ×
     A ⊑ A′
cc-prec-inv Γ⊑Γ′ _ (⊑-var Γ∋x Γ′∋x) = ⟨ ⊢var Γ∋x , ⊢var Γ′∋x , ⊑*→⊑ Γ⊑Γ′ Γ∋x Γ′∋x ⟩
cc-prec-inv _ _ ⊑-const = ⟨ ⊢const , ⊢const , ⊑-ty l⊑l ⊑-ι ⟩
cc-prec-inv _ Σ⊑Σ′ (⊑-addr {n = n} {ℓ} {ℓ̂} Σa≡T Σ′a≡T′) =
  ⟨ ⊢addr Σa≡T , ⊢addr Σ′a≡T′ , ⊑-ty l⊑l (⊑-ref (⊑-ty l⊑l (⊑ₘ→⊑ {n = n} {ℓ̂} Σ⊑Σ′ Σa≡T Σ′a≡T′))) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-lam g⊑g′ A⊑A′ N⊑N′) =
  let prec* = ⊑*-∷ A⊑A′ Γ⊑Γ′ in
  ⟨ ⊢lam (proj₁        (cc-prec-inv {ℓv′ = low} prec* Σ⊑Σ′ N⊑N′))  ,
    ⊢lam (proj₁ (proj₂ (cc-prec-inv {ℓv  = low} prec* Σ⊑Σ′ N⊑N′))) ,
    ⊑-ty l⊑l (⊑-fun g⊑g′ A⊑A′ (proj₂ (proj₂ (cc-prec-inv {ℓv = low} {low} prec* Σ⊑Σ′ N⊑N′)))) ⟩
{- Application -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-app {C = C} {C′} L⊑L′ M⊑M′ eq eq′) =
  let ⟨ ⊢L , ⊢L′ , A→B⊑A′→B′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _           ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  case A→B⊑A′→B′ of λ where
  (⊑-ty l⊑l (⊑-fun l⊑l A⊑A′ B⊑B′)) →
    let C⊑C′ : C ⊑ C′
        C⊑C′ = subst₂ _⊑_ (sym eq) (sym eq′) (stamp-⊑ B⊑B′ l⊑l) in
    ⟨ ⊢app ⊢L ⊢M eq , ⊢app ⊢L′ ⊢M′ eq′ , C⊑C′ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-app! {C = C} {C′} L⊑L′ M⊑M′ eq eq′) =
  let ⟨ ⊢L , ⊢L′ , A→B⊑A′→B′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _           ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  case A→B⊑A′→B′ of λ where
  (⊑-ty ⋆⊑ (⊑-fun ⋆⊑ A⊑A′ B⊑B′)) →
    let C⊑C′ : C ⊑ C′
        C⊑C′ = subst₂ _⊑_ (sym eq) (sym eq′) (stamp-⊑ B⊑B′ ⋆⊑) in
    ⟨ ⊢app! ⊢L ⊢M eq , ⊢app! ⊢L′ ⊢M′ eq′ , C⊑C′ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-app!l {C = C} {C′} L⊑L′ M⊑M′ eq eq′) =
  let ⟨ ⊢L , ⊢L′ , A→B⊑A′→B′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _           ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  case A→B⊑A′→B′ of λ where
  (⊑-ty ⋆⊑ (⊑-fun ⋆⊑ A⊑A′ B⊑B′)) →
    let C⊑C′ : C ⊑ C′
        C⊑C′ = subst₂ _⊑_ (sym eq) (sym eq′) (stamp-⊑ B⊑B′ ⋆⊑) in
    ⟨ ⊢app! ⊢L ⊢M eq , ⊢app ⊢L′ ⊢M′ eq′ , C⊑C′ ⟩
{- If -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-if L⊑L′ M⊑M′ N⊑N′ eq eq′) rewrite eq | eq′ =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ihm = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ihn = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ N⊑N′ in
  ⟨ ⊢if ⊢L (proj₁ (ihm _ low)) (proj₁ (ihn _ low)) refl ,
    ⊢if ⊢L′ (proj₁ (proj₂ (ihm low _))) (proj₁ (proj₂ (ihn low _))) refl ,
    stamp-⊑ (proj₂ (proj₂ (ihm low low))) l⊑l ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-if! L⊑L′ M⊑M′ N⊑N′ eq eq′) rewrite eq | eq′ =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ihm = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ihn = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ N⊑N′ in
  ⟨ ⊢if! ⊢L (proj₁ (ihm _ low)) (proj₁ (ihn _ low)) refl ,
    ⊢if! ⊢L′ (proj₁ (proj₂ (ihm low _))) (proj₁ (proj₂ (ihn low _))) refl ,
    stamp-⊑ (proj₂ (proj₂ (ihm low low))) ⋆⊑ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-if!l L⊑L′ M⊑M′ N⊑N′ eq eq′) rewrite eq | eq′ =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ihm = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ihn = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} Γ⊑Γ′ Σ⊑Σ′ N⊑N′ in
  ⟨ ⊢if! ⊢L (proj₁ (ihm _ low)) (proj₁ (ihn _ low)) refl ,
    ⊢if  ⊢L′ (proj₁ (proj₂ (ihm low _))) (proj₁ (proj₂ (ihn low _))) refl ,
    stamp-⊑ (proj₂ (proj₂ (ihm low low))) ⋆⊑ ⟩
{- Let -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-let M⊑M′ N⊑N′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let ih = λ ℓv ℓv′ → cc-prec-inv {ℓv = ℓv} {ℓv′} (⊑*-∷ A⊑A′ Γ⊑Γ′) Σ⊑Σ′ N⊑N′ in
  ⟨ ⊢let ⊢M (proj₁ (ih _ low)) ,
    ⊢let ⊢M′ (proj₁ (proj₂ (ih low _))) ,
    proj₂ (proj₂ (ih low low)) ⟩
{- Reference creation -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-ref M⊑M′ ℓc≼ℓ) =
  let ⟨ ⊢M , ⊢M′ , Tℓ⊑T′ℓ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢ref ⊢M ℓc≼ℓ , ⊢ref ⊢M′ ℓc≼ℓ , ⊑-ty l⊑l (⊑-ref Tℓ⊑T′ℓ) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-ref? M⊑M′) =
  let ⟨ ⊢M , ⊢M′ , Tℓ⊑T′ℓ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢ref? ⊢M , ⊢ref? ⊢M′ , ⊑-ty l⊑l (⊑-ref Tℓ⊑T′ℓ) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-ref?l M⊑M′ ℓc≼ℓ) =
  let ⟨ ⊢M , ⊢M′ , Tℓ⊑T′ℓ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢ref? ⊢M , ⊢ref ⊢M′ ℓc≼ℓ , ⊑-ty l⊑l (⊑-ref Tℓ⊑T′ℓ) ⟩
{- Dereference -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-deref M⊑M′ eq eq′) rewrite eq | eq′ =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ (⊑-ref A⊑A′) ⟩ →
    ⟨ ⊢deref ⊢M refl , ⊢deref ⊢M′ refl , stamp-⊑ A⊑A′ l⊑l ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-deref! M⊑M′ eq eq′) rewrite eq | eq′ =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ (⊑-ref A⊑A′) ⟩ →
    ⟨ ⊢deref! ⊢M refl , ⊢deref! ⊢M′ refl , stamp-⊑ A⊑A′ ⋆⊑ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-deref!l M⊑M′ eq eq′) rewrite eq | eq′ =
  case cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ of λ where
  ⟨ ⊢M , ⊢M′ , ⊑-ty _ (⊑-ref A⊑A′) ⟩ →
    ⟨ ⊢deref! ⊢M refl , ⊢deref ⊢M′ refl , stamp-⊑ A⊑A′ ⋆⊑ ⟩
{- Assignment -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-assign L⊑L′ M⊑M′ ℓc≼ℓ̂ ℓ≼ℓ̂) =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢assign ⊢L ⊢M ℓc≼ℓ̂ ℓ≼ℓ̂ , ⊢assign ⊢L′ ⊢M′ ℓc≼ℓ̂ ℓ≼ℓ̂ , ⊑-ty l⊑l ⊑-ι ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-assign? L⊑L′ M⊑M′) =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢assign? ⊢L ⊢M , ⊢assign? ⊢L′ ⊢M′ , ⊑-ty l⊑l ⊑-ι ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-assign?l L⊑L′ M⊑M′  ℓc≼ℓ̂ ℓ≼ℓ̂) =
  let ⟨ ⊢L , ⊢L′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ L⊑L′ in
  let ⟨ ⊢M , ⊢M′ , _ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢assign? ⊢L ⊢M , ⊢assign ⊢L′ ⊢M′ ℓc≼ℓ̂ ℓ≼ℓ̂ , ⊑-ty l⊑l ⊑-ι ⟩
{- Protection -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-prot M⊑M′ PC⊑PC′ x x′ eq eq′) rewrite eq | eq′ =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let prec = prec→⊑ PC⊑PC′ in
  let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
  ⟨ ⊢prot ⊢M ⊢PC x refl , ⊢prot ⊢M′ ⊢PC′ x′ refl , stamp-⊑ A⊑A′ l⊑l ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-prot! M⊑M′ PC⊑PC′ x x′ eq eq′ ℓ≼ℓ′) rewrite eq | eq′ =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let prec = prec→⊑ PC⊑PC′ in
  let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
  ⟨ ⊢prot! ⊢M ⊢PC x refl , ⊢prot! ⊢M′ ⊢PC′ x′ refl , stamp-⊑ A⊑A′ ⋆⊑ ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-prot!l M⊑M′ PC⊑PC′ x x′ eq eq′ ℓ≼ℓ′) rewrite eq | eq′ =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  let prec = prec→⊑ PC⊑PC′ in
  let ⟨ ⊢PC , ⊢PC′ ⟩ = prec→⊢ PC⊑PC′ in
  ⟨ ⊢prot! ⊢M ⊢PC x refl , ⊢prot ⊢M′ ⊢PC′ x′ refl , stamp-⊑ A⊑A′ ⋆⊑ ⟩
{- Cast -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-cast M⊑M′ c⊑c′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢cast ⊢M′ , proj₂ (coercion-prec→⊑ c⊑c′) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-castl M⊑M′ c⊑A′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢M′ , proj₂ (coercion-prec-left→⊑ c⊑A′) ⟩
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-castr M⊑M′ A⊑c′) =
  let ⟨ ⊢M , ⊢M′ , A⊑A′ ⟩ = cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ M⊑M′ in
  ⟨ ⊢M , ⊢cast ⊢M′ , proj₂ (coercion-prec-right→⊑ A⊑c′) ⟩
{- Blame -}
cc-prec-inv Γ⊑Γ′ Σ⊑Σ′ (⊑-blame ⊢M A⊑A′) =
  ⟨ ⊢M , ⊢blame , A⊑A′ ⟩



data _;_;_⊢_⊑_ : ∀ (Σ Σ′ : HeapContext) → ∀ ℓ → (μ μ′ : HalfHeap) → Set where

  ⊑-∅ : ∀ {Σ Σ′ ℓ} → Σ ; Σ′ ; ℓ ⊢ [] ⊑ []

  ⊑-∷ : ∀ {Σ Σ′ ℓ} {μ μ′ n} {V V′ v v′} {T T′}
    → Σ ; Σ′ ; ℓ ⊢ μ ⊑ μ′
    → [] ; [] ∣ Σ ; Σ′ ∣ l low ; l low ∣ low ; low ⊢ V ⊑ V′ ⇐ T of l ℓ ⊑ T′ of l ℓ
      --------------------------------------------------------------------------------
    → Σ ; Σ′ ; ℓ ⊢ (⟨ n , V & v ⟩ ∷ μ) ⊑ (⟨ n , V′ & v′ ⟩ ∷ μ′)

_;_⊢_⊑_ : ∀ (Σ Σ′ : HeapContext) (μ μ′ : Heap) → Set
Σ ; Σ′ ⊢ ⟨ μᴸ , μᴴ ⟩ ⊑ ⟨ μᴸ′ , μᴴ′ ⟩ = (Σ ; Σ′ ; low ⊢ μᴸ ⊑ μᴸ′) × (Σ ; Σ′ ; high ⊢ μᴴ ⊑ μᴴ′)
