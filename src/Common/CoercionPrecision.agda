open import Common.Types

module Common.CoercionPrecision where

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
open import Common.Coercions
open import CoercionExpr.Precision
  renaming (prec→⊑ to cexpr-prec→⊑; ⊢l_⊑_ to ⊢ₗ_⊑_; ⊢r_⊑_ to ⊢ᵣ_⊑_)
open import CoercionExpr.SyntacComp renaming (_⨟_ to _⊹⊹_)


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


comp-pres-prec : ∀ {A A′ B B′ C C′} {c : Cast A ⇒ B} {d : Cast B ⇒ C}
                                 {c′ : Cast A′ ⇒ B′} {d′ : Cast B′ ⇒ C′}
  → ⟨     c ⟩⊑⟨ c′      ⟩
  → ⟨     d ⟩⊑⟨ d′      ⟩
    -----------------------
  → ⟨ c ⨟ d ⟩⊑⟨ c′ ⨟ d′ ⟩
comp-pres-prec (⊑-base c̅⊑c̅′) (⊑-base d̅⊑d̅′) = ⊑-base (comp-pres-⊑ c̅⊑c̅′ d̅⊑d̅′)
comp-pres-prec (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  ⊑-ref (comp-pres-prec c⊑A′ c⊑c′) (comp-pres-prec d⊑d′ d⊑A′)
        (comp-pres-⊑ c̅⊑c̅′ c̅⊑g′)
comp-pres-prec (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) =
  ⊑-fun (comp-pres-⊑ d̅⊑gc′ d̅⊑d̅′) (comp-pres-prec c⊑A′ c⊑c′)
        (comp-pres-prec d⊑d′ d⊑B′) (comp-pres-⊑ c̅⊑c̅′ c̅⊑g′)


comp-pres-prec-ll : ∀ {A A′ B C} {c : Cast A ⇒ B} {d : Cast B ⇒ C}
  → ⟨     c ⟩⊑ A′
  → ⟨     d ⟩⊑ A′
    -----------------------
  → ⟨ c ⨟ d ⟩⊑ A′
comp-pres-prec-ll (⊑-base c̅⊑g′) (⊑-base d̅⊑g′) = ⊑-base (comp-pres-⊑-ll c̅⊑g′ d̅⊑g′)
comp-pres-prec-ll (⊑-ref c₁⊑A′ d₁⊑A′ c̅⊑g′) (⊑-ref c₂⊑A′ d₂⊑A′ d̅⊑g′) =
  ⊑-ref (comp-pres-prec-ll c₂⊑A′ c₁⊑A′) (comp-pres-prec-ll d₁⊑A′ d₂⊑A′)
        (comp-pres-⊑-ll c̅⊑g′ d̅⊑g′)
comp-pres-prec-ll (⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′) (⊑-fun d̅₂⊑gc′ c₂⊑A′ d₂⊑B′ c̅₂⊑g′) =
  ⊑-fun (comp-pres-⊑-ll d̅₂⊑gc′ d̅₁⊑gc′) (comp-pres-prec-ll c₂⊑A′ c₁⊑A′)
        (comp-pres-prec-ll d₁⊑B′ d₂⊑B′) (comp-pres-⊑-ll c̅₁⊑g′ c̅₂⊑g′)

comp-pres-prec-rr : ∀ {A A′ B′ C′} {c : Cast A′ ⇒ B′} {d : Cast B′ ⇒ C′}
  → A ⊑⟨     c ⟩
  → A ⊑⟨     d ⟩
    -----------------------
  → A ⊑⟨ c ⨟ d ⟩
comp-pres-prec-rr (⊑-base c̅⊑g′) (⊑-base d̅⊑g′) = ⊑-base (comp-pres-⊑-rr c̅⊑g′ d̅⊑g′)
comp-pres-prec-rr (⊑-ref c₁⊑A′ d₁⊑A′ c̅⊑g′) (⊑-ref c₂⊑A′ d₂⊑A′ d̅⊑g′) =
  ⊑-ref (comp-pres-prec-rr c₂⊑A′ c₁⊑A′) (comp-pres-prec-rr d₁⊑A′ d₂⊑A′)
        (comp-pres-⊑-rr c̅⊑g′ d̅⊑g′)
comp-pres-prec-rr (⊑-fun d̅₁⊑gc′ c₁⊑A′ d₁⊑B′ c̅₁⊑g′) (⊑-fun d̅₂⊑gc′ c₂⊑A′ d₂⊑B′ c̅₂⊑g′) =
  ⊑-fun (comp-pres-⊑-rr d̅₂⊑gc′ d̅₁⊑gc′) (comp-pres-prec-rr c₂⊑A′ c₁⊑A′)
        (comp-pres-prec-rr d₁⊑B′ d₂⊑B′) (comp-pres-⊑-rr c̅₁⊑g′ c̅₂⊑g′)


comp-pres-prec-bl : ∀ {A A′ B B′ C} {c : Cast A ⇒ B} {d : Cast B ⇒ C}
                      {c′ : Cast A′ ⇒ B′}
  → ⟨     c ⟩⊑⟨ c′ ⟩
  → ⟨     d ⟩⊑ B′
    -----------------------
  → ⟨ c ⨟ d ⟩⊑⟨ c′ ⟩

comp-pres-prec-lb : ∀ {A A′ B B′ C} {c : Cast A ⇒ B} {d : Cast B ⇒ C}
                      {c′ : Cast A′ ⇒ B′}
  → ⟨     c ⟩⊑ A′
  → ⟨     d ⟩⊑⟨ c′ ⟩
    -----------------------
  → ⟨ c ⨟ d ⟩⊑⟨ c′ ⟩

comp-pres-prec-bl (⊑-base c̅⊑c̅′) (⊑-base d̅⊑g′) = ⊑-base (comp-pres-⊑-bl c̅⊑c̅′ d̅⊑g′)
comp-pres-prec-bl (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  ⊑-ref (comp-pres-prec-lb c⊑A′ c⊑c′) (comp-pres-prec-bl d⊑d′ d⊑A′)
        (comp-pres-⊑-bl c̅⊑c̅′ c̅⊑g′)
comp-pres-prec-bl (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) =
  ⊑-fun (comp-pres-⊑-lb d̅⊑gc′ d̅⊑d̅′) (comp-pres-prec-lb c⊑A′ c⊑c′)
        (comp-pres-prec-bl d⊑d′ d⊑B′) (comp-pres-⊑-bl c̅⊑c̅′ c̅⊑g′)

comp-pres-prec-lb (⊑-base d̅⊑g′) (⊑-base c̅⊑c̅′) = ⊑-base (comp-pres-⊑-lb d̅⊑g′ c̅⊑c̅′)
comp-pres-prec-lb (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) =
  ⊑-ref (comp-pres-prec-bl c⊑c′ c⊑A′) (comp-pres-prec-lb d⊑A′ d⊑d′)
        (comp-pres-⊑-lb c̅⊑g′ c̅⊑c̅′)
comp-pres-prec-lb (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) (⊑-fun d̅⊑d̅′ c⊑c′ d⊑d′ c̅⊑c̅′) =
  ⊑-fun (comp-pres-⊑-bl d̅⊑d̅′ d̅⊑gc′) (comp-pres-prec-bl c⊑c′ c⊑A′)
        (comp-pres-prec-lb d⊑B′ d⊑d′) (comp-pres-⊑-lb c̅⊑g′ c̅⊑c̅′)

comp-pres-prec-br : ∀ {A A′ B B′ C′} {c : Cast A ⇒ B}
                      {c′ : Cast A′ ⇒ B′} {d′ : Cast B′ ⇒ C′}
  → ⟨     c ⟩⊑⟨ c′ ⟩
  →        B ⊑⟨ d′ ⟩
    -----------------------
  → ⟨ c ⟩⊑⟨ c′ ⨟ d′ ⟩

comp-pres-prec-rb : ∀ {A A′ B B′ C′} {c : Cast A ⇒ B}
                      {c′ : Cast A′ ⇒ B′} {d′ : Cast B′ ⇒ C′}
  →        A ⊑⟨ c′ ⟩
  → ⟨     c ⟩⊑⟨ d′ ⟩
    -----------------------
  → ⟨ c ⟩⊑⟨ c′ ⨟ d′ ⟩

comp-pres-prec-br (⊑-base x) (⊑-base x′) = ⊑-base (comp-pres-⊑-br x x′)
comp-pres-prec-br (⊑-ref x y z) (⊑-ref x′ y′ z′) =
  ⊑-ref (comp-pres-prec-rb x′ x) (comp-pres-prec-br y y′)
        (comp-pres-⊑-br z z′)
comp-pres-prec-br (⊑-fun x y z w) (⊑-fun x′ y′ z′ w′) =
  ⊑-fun (comp-pres-⊑-rb x′ x) (comp-pres-prec-rb y′ y)
        (comp-pres-prec-br z z′) (comp-pres-⊑-br w w′)

comp-pres-prec-rb (⊑-base x) (⊑-base x′) = ⊑-base (comp-pres-⊑-rb x x′)
comp-pres-prec-rb (⊑-ref x y z) (⊑-ref x′ y′ z′) =
  ⊑-ref (comp-pres-prec-br x′ x) (comp-pres-prec-rb y y′)
        (comp-pres-⊑-rb z z′)
comp-pres-prec-rb (⊑-fun x y z w) (⊑-fun x′ y′ z′ w′) =
  ⊑-fun (comp-pres-⊑-br x′ x) (comp-pres-prec-br y′ y)
        (comp-pres-prec-rb z z′) (comp-pres-⊑-rb w w′)

comp-pres-prec-rl : ∀ {A A′ B B′} {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
  → A ⊑⟨ c′ ⟩
  → ⟨ c ⟩⊑ B′
    -----------------------
  → ⟨ c ⟩⊑⟨ c′ ⟩

comp-pres-prec-lr : ∀ {A A′ B B′} {c : Cast A ⇒ B} {c′ : Cast A′ ⇒ B′}
  → ⟨ c ⟩⊑ A′
  → B ⊑⟨ c′ ⟩
    -----------------------
  → ⟨ c ⟩⊑⟨ c′ ⟩

comp-pres-prec-rl (⊑-base g⊑c̅′) (⊑-base c̅⊑g′) = ⊑-base (comp-pres-⊑-rl g⊑c̅′ c̅⊑g′)
comp-pres-prec-rl (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  ⊑-ref (comp-pres-prec-lr c⊑A′ A⊑c′) (comp-pres-prec-rl A⊑d′ d⊑A′)
        (comp-pres-⊑-rl g⊑c̅′ c̅⊑g′)
comp-pres-prec-rl (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′) (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) =
  ⊑-fun (comp-pres-⊑-lr d̅⊑gc′ gc⊑d̅′) (comp-pres-prec-lr c⊑A′ A⊑c′)
        (comp-pres-prec-rl B⊑d′ d⊑B′) (comp-pres-⊑-rl g⊑c̅′ c̅⊑g′)

comp-pres-prec-lr (⊑-base c̅⊑g′) (⊑-base g⊑c̅′) = ⊑-base (comp-pres-⊑-lr c̅⊑g′ g⊑c̅′)
comp-pres-prec-lr (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) =
  ⊑-ref (comp-pres-prec-rl A⊑c′ c⊑A′) (comp-pres-prec-lr d⊑A′ A⊑d′)
        (comp-pres-⊑-lr c̅⊑g′ g⊑c̅′)
comp-pres-prec-lr (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) (⊑-fun gc⊑d̅′ A⊑c′ B⊑d′ g⊑c̅′) =
  ⊑-fun (comp-pres-⊑-rl gc⊑d̅′ d̅⊑gc′) (comp-pres-prec-rl A⊑c′ c⊑A′)
        (comp-pres-prec-lr d⊑B′ B⊑d′) (comp-pres-⊑-lr c̅⊑g′ g⊑c̅′)


prec-coerce-id : ∀ {A A′}
  → A ⊑ A′
  → ⟨ coerce-id A ⟩⊑ A′
prec-coerce-id (⊑-ty g₁⊑g₂ ⊑-ι) = ⊑-base (⊑-id g₁⊑g₂)
prec-coerce-id (⊑-ty g₁⊑g₂ (⊑-ref A⊑B)) =
  ⊑-ref (prec-coerce-id A⊑B) (prec-coerce-id A⊑B) (⊑-id g₁⊑g₂)
prec-coerce-id (⊑-ty x (⊑-fun x₁ x₂ x₃)) =
  ⊑-fun (⊑-id x₁) (prec-coerce-id x₂) (prec-coerce-id x₃) (⊑-id x)

prec-left-coerce-id : ∀ {A A′ B} {c : Cast A ⇒ B}
  → ⟨ c ⟩⊑ A′
  → ⟨ c ⟩⊑⟨ coerce-id A′ ⟩
prec-left-coerce-id (⊑-base c̅⊑g′) = ⊑-base (⊑-left-expand c̅⊑g′)
prec-left-coerce-id (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  ⊑-ref (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑A′) (⊑-left-expand c̅⊑g′)
prec-left-coerce-id (⊑-fun d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) =
  ⊑-fun (⊑-left-expand d̅⊑gc′) (prec-left-coerce-id c⊑A′) (prec-left-coerce-id d⊑B′) (⊑-left-expand c̅⊑g′)


stamp⋆-left-prec : ∀ {A A′} {ℓ}
  → A ⊑ A′
    ----------------------------------------------
  → ⟨ stamp A , ℓ ⇒stamp⋆ ⟩⊑ stamp A′ (l ℓ)
stamp⋆-left-prec (⊑-ty ⋆⊑ ⊑-ι) = ⊑-base (⊑-id ⋆⊑)
stamp⋆-left-prec (⊑-ty ⋆⊑ (⊑-ref A⊑A′)) =
  ⊑-ref (prec-coerce-id A⊑A′) (prec-coerce-id A⊑A′) (⊑-id ⋆⊑)
stamp⋆-left-prec (⊑-ty ⋆⊑ (⊑-fun gᶜ⊑gᶜ′ A⊑A′ B⊑B′)) =
  ⊑-fun (⊑-id gᶜ⊑gᶜ′) (prec-coerce-id A⊑A′) (prec-coerce-id B⊑B′) (⊑-id ⋆⊑)
stamp⋆-left-prec (⊑-ty l⊑l ⊑-ι) = ⊑-base (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
stamp⋆-left-prec (⊑-ty l⊑l (⊑-ref A⊑A′)) =
  ⊑-ref (prec-coerce-id A⊑A′) (prec-coerce-id A⊑A′) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
stamp⋆-left-prec (⊑-ty l⊑l (⊑-fun gᶜ⊑gᶜ′ A⊑A′ B⊑B′)) =
  ⊑-fun (⊑-id gᶜ⊑gᶜ′) (prec-coerce-id A⊑A′) (prec-coerce-id B⊑B′) (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
