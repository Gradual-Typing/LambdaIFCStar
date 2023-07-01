module LabelExpr.LabelExpr where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
  renaming (_∎ to _∎ₗ ; _—→⟨_⟩_ to _—→ₗ⟨_⟩_)
  hiding (Progress; progress; plug-cong; ↠-trans)
open import CoercionExpr.SyntacComp
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SecurityLevel renaming (∥_∥ to ∥_∥ₗ)
open import CoercionExpr.Stamping


data LExpr : Set where

  l : StaticLabel → LExpr

  _⟪_⟫ : ∀ {g₁ g₂} → LExpr → CExpr g₁ ⇒ g₂ → LExpr

  blame : BlameLabel → LExpr


data Irreducible : ∀ {g₁ g₂} (c̅ : CExpr g₁ ⇒ g₂) → Set where

  ir : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂}
    → CVal c̅
    → .(g₁ ≢ g₂)
    → Irreducible c̅


data LVal : LExpr → Set where

  {- raw value -}
  v-l : ∀ {ℓ} → LVal (l ℓ)

  {- wrapped value (one cast) -}
  v-cast : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g}
    → Irreducible c̅
    → LVal (l ℓ ⟪ c̅ ⟫)

data LResult : LExpr → Set where

  success : ∀ {V} → LVal V → LResult V

  fail : ∀ {p} → LResult (blame p)


data ⊢_⇐_ : LExpr → Label → Set where

  ⊢l : ∀ {ℓ} → ⊢ l ℓ ⇐ l ℓ

  ⊢cast : ∀ {g₁ g₂} {M} {c̅ : CExpr g₁ ⇒ g₂}
    → ⊢ M ⇐ g₁
      ------------------
    → ⊢ M ⟪ c̅ ⟫ ⇐ g₂

  ⊢blame : ∀ {g} {p} → ⊢ blame p ⇐ g


infix 2 _—→ₑ_

data _—→ₑ_ : (M N : LExpr) → Set where

  ξ : ∀ {g₁ g₂} {M N} {c̅ : CExpr g₁ ⇒ g₂}
    → M —→ₑ N
      --------------------------
    → M ⟪ c̅ ⟫ —→ₑ N ⟪ c̅ ⟫

  ξ-blame : ∀ {g₁ g₂} {c̅ : CExpr g₁ ⇒ g₂} {p}
      -----------------------------------------------
    → blame p ⟪ c̅ ⟫ —→ₑ blame p

  β-id : ∀ {ℓ} → l ℓ ⟪ id (l ℓ) ⟫ —→ₑ l ℓ

  cast : ∀ {ℓ g} {c̅ c̅ₙ : CExpr l ℓ ⇒ g}
    → c̅ —→⁺ c̅ₙ
    → CVal c̅ₙ
      -------------------------------
    → l ℓ ⟪ c̅ ⟫ —→ₑ l ℓ ⟪ c̅ₙ ⟫

  blame : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g} {p}
    → c̅ —↠ ⊥ (l ℓ) g p
      --------------------------
    → l ℓ ⟪ c̅ ⟫ —→ₑ blame p

  comp : ∀ {ℓ g₁ g₂} {c̅ᵢ : CExpr l ℓ ⇒ g₁} {d̅ : CExpr g₁ ⇒ g₂}
    → Irreducible c̅ᵢ
      -------------------------------------------
    → l ℓ ⟪ c̅ᵢ ⟫ ⟪ d̅ ⟫ —→ₑ l ℓ ⟪ c̅ᵢ ⨟ d̅ ⟫



data Progress : LExpr → Set where

  done : ∀ {M} → LVal M → Progress M

  error : ∀ {p} → Progress (blame p)

  step : ∀ {M N} → M  —→ₑ N → Progress M

progress : ∀ {g M} → ⊢ M ⇐ g → Progress M
progress ⊢l = done v-l
progress (⊢cast {c̅ = c̅} ⊢M) =
  case progress ⊢M of λ where
  (done v) →
    case ⟨ v , ⊢M ⟩ of λ where
    ⟨ v-l , ⊢l ⟩ →
      case cexpr-sn c̅ of λ where
      ⟨ d̅ , _ ∎ₗ , success id ⟩ → step β-id
      ⟨ d̅ , _ ∎ₗ , success (inj 𝓋) ⟩ → done (v-cast (ir (inj 𝓋) λ ()))
      ⟨ d̅ , _ ∎ₗ , success (up id) ⟩ → done (v-cast (ir (up id) λ ()))
      ⟨ d̅ , _ —→ₗ⟨ c̅→c̅′ ⟩ c̅′↠d̅ , success 𝓋 ⟩ → step (cast (_ —→ₗ⟨ c̅→c̅′ ⟩ c̅′↠d̅) 𝓋)
      ⟨ _ , c̅↠⊥ , fail      ⟩ → step (blame c̅↠⊥)
    ⟨ v-cast {c̅ = c̅′} i , ⊢cast _ ⟩ → step (comp i)
  (error) → step ξ-blame
  (step M→N) → step (ξ M→N)
progress ⊢blame = error

preserve : ∀ {g M N}
  → ⊢ M ⇐ g
  → M —→ₑ N
  → ⊢ N ⇐ g
preserve (⊢cast ⊢M) (ξ M→N) = ⊢cast (preserve ⊢M M→N)
preserve (⊢cast ⊢M) ξ-blame = ⊢blame
preserve (⊢cast ⊢M) β-id = ⊢l
preserve (⊢cast ⊢M) (cast x x₁) = ⊢cast ⊢l
preserve (⊢cast ⊢M) (blame _) = ⊢blame
preserve (⊢cast ⊢M) (comp _) = ⊢cast ⊢l

open import Common.MultiStep ⊤ (λ {tt tt → LExpr}) _—→ₑ_ public
  renaming (_—↠_ to _—↠ₑ_; ↠-trans to ↠ₑ-trans)

plug-congₑ : ∀ {g₁ g₂} {M N : LExpr} {c̅ : CExpr g₁ ⇒ g₂}
  → M —↠ₑ N
  → M ⟪ c̅ ⟫ —↠ₑ N ⟪ c̅ ⟫
plug-congₑ (M ∎) = (M ⟪ _ ⟫) ∎
plug-congₑ (M —→⟨ M→L ⟩ L↠N) = M ⟪ _ ⟫ —→⟨ ξ M→L ⟩ (plug-congₑ L↠N)

preserve-mult : ∀ {g} {M N} → ⊢ M ⇐ g → M —↠ₑ N → ⊢ N ⇐ g
preserve-mult ⊢M (_ ∎) = ⊢M
preserve-mult ⊢L (L —→⟨ L→M ⟩ M↠N) = preserve-mult (preserve ⊢L L→M) M↠N


data ⊢_⊑_⇐_⊑_ : ∀ (M M′ : LExpr) (g₁ g₂ : Label) → Set where

  ⊑-l : ∀ {ℓ} → ⊢ l ℓ ⊑ l ℓ ⇐ l ℓ ⊑ l ℓ

  ⊑-cast : ∀ {g₁ g₁′ g₂ g₂′} {M M′}
             {c̅ : CExpr g₁ ⇒ g₂} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ M ⊑ M′ ⇐ g₁ ⊑ g₁′
    → ⊢ c̅ ⊑ c̅′
      --------------------------------------
    → ⊢ M ⟪ c̅ ⟫ ⊑ M′ ⟪ c̅′ ⟫ ⇐ g₂ ⊑ g₂′

  ⊑-castl : ∀ {g₁ g₂ g′} {M M′} {c̅ : CExpr g₁ ⇒ g₂}
    → ⊢ M ⊑ M′ ⇐ g₁ ⊑ g′
    → ⊢l c̅ ⊑ g′
      --------------------------------------
    → ⊢ M ⟪ c̅ ⟫ ⊑ M′ ⇐ g₂ ⊑ g′

  ⊑-castr : ∀ {g g₁′ g₂′} {M M′} {c̅′ : CExpr g₁′ ⇒ g₂′}
    → ⊢ M ⊑ M′ ⇐ g ⊑ g₁′
    → ⊢r g ⊑ c̅′
      --------------------------------------
    → ⊢ M ⊑ M′ ⟪ c̅′ ⟫ ⇐ g ⊑ g₂′

  ⊑-blame : ∀ {g g′} {M} {p}
    → ⊢ M ⇐ g
    → g ⊑ₗ g′
      --------------------------
    → ⊢ M ⊑ blame p ⇐ g ⊑ g′


{- Precision implies that both sides are well-typed -}
prec→⊢ : ∀ {g g′} {M M′}
  → ⊢ M ⊑ M′ ⇐ g ⊑ g′
  → ⊢ M ⇐ g  ×  ⊢ M′ ⇐ g′
prec→⊢ ⊑-l = ⟨ ⊢l , ⊢l ⟩
prec→⊢ (⊑-cast M⊑M′ c̅⊑c̅′) =
  let ⟨ ⊢M , ⊢M′ ⟩ = prec→⊢ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢cast ⊢M′ ⟩
prec→⊢ (⊑-castl M⊑M′ _) =
  let ⟨ ⊢M , ⊢M′ ⟩ = prec→⊢ M⊑M′ in
  ⟨ ⊢cast ⊢M , ⊢M′ ⟩
prec→⊢ (⊑-castr M⊑M′ _) =
  let ⟨ ⊢M , ⊢M′ ⟩ = prec→⊢ M⊑M′ in
  ⟨ ⊢M , ⊢cast ⊢M′ ⟩
prec→⊢ (⊑-blame ⊢M _) = ⟨ ⊢M , ⊢blame ⟩


{- Term precision implies type precision -}
prec→⊑ : ∀ {g₁ g₂} {M N} → ⊢ M ⊑ N ⇐ g₁ ⊑ g₂ → g₁ ⊑ₗ g₂
prec→⊑ ⊑-l = l⊑l
prec→⊑ (⊑-cast _ c̅⊑c̅′)   = proj₂ (precₗ→⊑ _ _ c̅⊑c̅′)
prec→⊑ (⊑-castl _ c̅⊑g′)  = proj₂ (prec-left→⊑ _ c̅⊑g′)
prec→⊑ (⊑-castr _ g⊑c̅′)  = proj₂ (prec-right→⊑ _ g⊑c̅′)
prec→⊑ (⊑-blame ⊢M g⊑g′) = g⊑g′


{- Precision of label expressions implies the precision of coercion expressions -}
prec-inv : ∀ {ℓ ℓ′ g g′} {c̅ : CExpr l ℓ ⇒ g} {c̅′ : CExpr l ℓ′ ⇒ g′}
  → ⊢ l ℓ ⟪ c̅ ⟫ ⊑ l ℓ′ ⟪ c̅′ ⟫ ⇐ g ⊑ g′
  → ℓ ≡ ℓ′  ×  ⊢ c̅ ⊑ c̅′
prec-inv (⊑-cast ⊑-l c̅⊑c̅′)                 = ⟨ refl , c̅⊑c̅′ ⟩
prec-inv (⊑-castl (⊑-castr ⊑-l ℓ⊑c̅′) c̅⊑g′) = ⟨ refl , comp-pres-⊑-rl ℓ⊑c̅′ c̅⊑g′ ⟩
prec-inv (⊑-castr (⊑-castl ⊑-l c̅⊑ℓ) g⊑c̅′)  = ⟨ refl , comp-pres-⊑-lr c̅⊑ℓ g⊑c̅′  ⟩


{- Security level -}
∥_∥ : ∀ (V : LExpr) → LVal V → StaticLabel
∥ l ℓ       ∥ v-l                = ℓ
∥ l ℓ ⟪ c̅ ⟫ ∥ (v-cast (ir 𝓋 _)) = ∥ c̅ ∥ₗ 𝓋


{- Stamping -}
stampₑ : ∀ V → LVal V → StaticLabel → LExpr
stampₑ (l ℓ) v-l low     = l ℓ
stampₑ (l low) v-l high  = l low ⟪ id (l low) ⨾ ↑ ⟫
stampₑ (l high) v-l high = l high
stampₑ (l ℓ ⟪ c̅ ⟫) (v-cast (ir 𝓋 _)) ℓ′ = l ℓ ⟪ stampₗ c̅ 𝓋 ℓ′ ⟫

stampₑ-wt : ∀ {V g ℓ}
  → (v : LVal V)
  → ⊢ V ⇐ g
  → ⊢ stampₑ V v ℓ ⇐ (g ⋎̃ l ℓ)
stampₑ-wt {g = g} {low} v-l ⊢V rewrite g⋎̃low≡g {g} = ⊢V
stampₑ-wt {ℓ = high} (v-l {low}) ⊢l = ⊢cast ⊢l
stampₑ-wt {ℓ = high} (v-l {high}) ⊢l = ⊢l
stampₑ-wt (v-cast (ir 𝓋 _)) (⊢cast ⊢l) = ⊢cast ⊢l

stampₑ-LVal : ∀ {V ℓ}
  → (v : LVal V)
  → LVal (stampₑ V v ℓ)
stampₑ-LVal {V} {low} v-l = v-l
stampₑ-LVal {V} {high} (v-l {low}) = v-cast (ir (up id) (λ ()))
stampₑ-LVal {V} {high} (v-l {high}) = v-l
stampₑ-LVal {V} {ℓ} (v-cast (ir 𝓋 x)) =
  v-cast (ir (stampₗ-CVal _ 𝓋 ℓ) (stamp-not-id 𝓋 x))


lexpr-sn : ∀ {A} L
  → ⊢ L ⇐ A
    ----------------------------------------
  → ∃[ M ] (L —↠ₑ M) × LResult M
lexpr-sn (l ℓ) ⊢l = ⟨ l ℓ , _ ∎ , success v-l ⟩
lexpr-sn (L ⟪ c̅ ⟫) (⊢cast ⊢L) =
  case lexpr-sn L ⊢L of λ where
  ⟨ blame p , L↠blame , fail ⟩ →
    ⟨ blame p , ↠ₑ-trans (plug-congₑ L↠blame) (_ —→⟨ ξ-blame ⟩ _ ∎) ,
      fail ⟩
  ⟨ l ℓ , L↠V , success v-l ⟩ →
    case ⟨ preserve-mult ⊢L L↠V , cexpr-sn c̅ ⟩ of λ where
    ⟨ ⊢l , ⊥ _ _ q , c̅↠d̅ , fail ⟩ →
      ⟨ blame q , ↠ₑ-trans (plug-congₑ L↠V)
                            (_ —→⟨ blame c̅↠d̅ ⟩ _ ∎) ,
        fail ⟩
    ⟨ ⊢l , c̅ₙ , _ ∎ₗ , success id ⟩ →
      ⟨ l ℓ , ↠ₑ-trans (plug-congₑ L↠V)
                        (_ —→⟨ β-id ⟩ _ ∎) ,
        success v-l ⟩
    ⟨ ⊢l , c̅ₙ , _ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success id ⟩ →
      ⟨ l ℓ , ↠ₑ-trans (plug-congₑ L↠V)
                        (_ —→⟨ cast (_ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
        success v-l ⟩
    ⟨ ⊢l , c̅ₙ , _ ∎ₗ , success (up id) ⟩ →
      ⟨ l ℓ ⟪ _ ⟫ , plug-congₑ L↠V ,
        success (v-cast (ir (up id) (λ ()))) ⟩
    ⟨ ⊢l , c̅ₙ , _ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success (up id) ⟩ →
      ⟨ l ℓ ⟪ _ ⟫ , ↠ₑ-trans (plug-congₑ L↠V)
                              (_ —→⟨ cast (_ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) (up id) ⟩ _ ∎) ,
        success (v-cast (ir (up id) (λ ()))) ⟩
    ⟨ ⊢l , c̅ₙ , _ ∎ₗ , success (inj 𝓋) ⟩ →
      ⟨ l ℓ ⟪ _ ⟫ , plug-congₑ L↠V ,
        success (v-cast (ir (inj 𝓋) (λ ()))) ⟩
    ⟨ ⊢l , c̅ₙ , _ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ , success (inj 𝓋) ⟩ →
      ⟨ l ℓ ⟪ _ ⟫ , ↠ₑ-trans (plug-congₑ L↠V)
                              (_ —→⟨ cast (_ —→ₗ⟨ c̅→d̅ ⟩ d̅↠c̅ₙ) (inj 𝓋) ⟩ _ ∎) ,
        success (v-cast (ir (inj 𝓋) (λ ()))) ⟩
  ⟨ l ℓ ⟪ c̅ᵢ ⟫ , L↠V , success (v-cast i) ⟩ →
    case preserve-mult ⊢L L↠V of λ where
    (⊢cast ⊢l) →
      case cexpr-sn (c̅ᵢ ⨟ c̅) of λ where
      ⟨ ⊥ _ _ q , c̅↠d̅ , fail ⟩ →
        ⟨ blame q , ↠ₑ-trans (plug-congₑ L↠V)
                    (_ —→⟨ comp i ⟩ _ —→⟨ blame c̅↠d̅ ⟩ _ ∎) ,
          fail ⟩
      ⟨ c̅ₙ , c̅↠d̅ , success id ⟩ →
        ⟨ l ℓ , ↠ₑ-trans (plug-congₑ L↠V)
                (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅↠d̅ id) id ⟩ _ —→⟨ β-id ⟩ _ ∎) ,
          success v-l ⟩
      ⟨ c̅ₙ , c̅↠c̅ₙ , success (up id) ⟩ →
        ⟨ l ℓ ⟪ _ ⟫ , ↠ₑ-trans (plug-congₑ L↠V)
                      (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅↠c̅ₙ (up id)) (up id) ⟩ _ ∎) ,
          success (v-cast (ir (up id) (λ ()))) ⟩
      ⟨ c̅ₙ , c̅↠c̅ₙ , success (inj 𝓋) ⟩ →
        ⟨ l ℓ ⟪ _ ⟫ , ↠ₑ-trans (plug-congₑ L↠V)
                      (_ —→⟨ comp i ⟩ _ —→⟨ cast (comp-→⁺ c̅↠c̅ₙ (inj 𝓋)) (inj 𝓋) ⟩ _ ∎) ,
          success (v-cast (ir (inj 𝓋) (λ ()))) ⟩
lexpr-sn (blame p) ⊢blame = ⟨ blame p , _ ∎ , fail ⟩


uniq-LVal : ∀ {V} → (v w : LVal V) → v ≡ w
uniq-LVal v-l v-l = refl
uniq-LVal (v-cast (ir 𝓋 x)) (v-cast (ir 𝓋′ y)) rewrite uniq-CVal 𝓋 𝓋′ = refl


stampₑ-security : ∀ {V ℓ} (v : LVal V) → (∥ V ∥ v) ⋎ ℓ ≡ ∥ stampₑ V v ℓ ∥ (stampₑ-LVal v)
stampₑ-security {V = l ℓ}    {ℓ = low}  v-l rewrite ℓ⋎low≡ℓ {ℓ} = refl
stampₑ-security {V = l low}  {ℓ = high} v-l = refl
stampₑ-security {V = l high} {ℓ = high} v-l = refl
stampₑ-security {V} {low}  (v-cast (ir 𝓋 _)) = stampₗ-security _ 𝓋 low
stampₑ-security {V} {high} (v-cast (ir 𝓋 _)) = stampₗ-security _ 𝓋 high

LVal⌿→ : ∀ {V M} → LVal V → ¬ (V —→ₑ M)
LVal⌿→ (v-cast (ir id x)) β-id = contradiction refl (recompute (¬? (_ ==? _)) x)
LVal⌿→ (v-cast (ir 𝓋 _)) (cast (_ —→ₗ⟨ r ⟩ _) _) = CVal⌿→ 𝓋 r
LVal⌿→ (v-cast (ir 𝓋 _)) (blame (_ —→ₗ⟨ r ⟩ _))  = CVal⌿→ 𝓋 r


detₑ : ∀ {L M N}
  → L —→ₑ M
  → L —→ₑ N
    ----------------------------
  → M ≡ N
detₑ (ξ L→M) (ξ L→N) = cong _⟪ _ ⟫ (detₑ L→M L→N)
detₑ (ξ L→M) (comp i) = contradiction L→M (LVal⌿→ (v-cast i))
detₑ ξ-blame ξ-blame = refl
detₑ β-id β-id = refl
detₑ β-id (cast (_ —→ₗ⟨ r ⟩ _) _) = contradiction r (CVal⌿→ id)
detₑ β-id (blame (_ —→ₗ⟨ r ⟩ _)) = contradiction r (CVal⌿→ id)
detₑ (cast (_ —→ₗ⟨ r ⟩ _) _) β-id = contradiction r (CVal⌿→ id)
detₑ (cast c̅→⁺d̅₁ 𝓋₁) (cast c̅→⁺d̅₂ 𝓋₂) =
  cong (_ ⟪_⟫) (det-mult (→⁺-impl-↠ c̅→⁺d̅₁) (→⁺-impl-↠ c̅→⁺d̅₂)
                         (success 𝓋₁) (success 𝓋₂))
detₑ (cast c̅→⁺c̅ₙ 𝓋) (blame c̅↠⊥)
  with det-mult (→⁺-impl-↠ c̅→⁺c̅ₙ) c̅↠⊥ (success 𝓋) fail
... | refl = case 𝓋 of λ ()
detₑ (blame (_ —→ₗ⟨ r ⟩ _)) β-id = contradiction r (CVal⌿→ id)
detₑ (blame c̅↠⊥) (cast c̅→⁺c̅ₙ 𝓋)
  with det-mult (→⁺-impl-↠ c̅→⁺c̅ₙ) c̅↠⊥ (success 𝓋) fail
... | refl = case 𝓋 of λ ()
detₑ (blame c̅↠⊥₁) (blame c̅↠⊥₂)
  with det-mult c̅↠⊥₁ c̅↠⊥₂ fail fail
... | refl = refl
detₑ (comp i) (ξ L→N) = contradiction L→N (LVal⌿→ (v-cast i))
detₑ (comp _) (comp _) = refl


det-multₑ : ∀ {M V W}
  → M —↠ₑ V
  → M —↠ₑ W
  → LVal V → LVal W
    -----------------------
  → V ≡ W
det-multₑ (V ∎) (W ∎) _ _ = refl
det-multₑ (_ ∎) (_ —→⟨ r ⟩ ↠W) v = contradiction r (LVal⌿→ v)
det-multₑ (_ —→⟨ r ⟩ ↠V) (_ ∎) _ v = contradiction r (LVal⌿→ v)
det-multₑ (L —→⟨ L→M ⟩ M↠V) (L —→⟨ L→N ⟩ N↠W) v w
  with detₑ L→M L→N
... | refl = det-multₑ M↠V N↠W v w


stamp⇒⋆-security : ∀ {g ℓ V V′}
  → (v : LVal V)
  → ⊢ V ⇐ g
  → stampₑ V v ℓ ⟪ coerce (g ⋎̃ l ℓ) ⇒⋆ ⟫ —↠ₑ V′
  → (v′ : LVal V′)
    ---------------------------------
  → (∥ V ∥ v) ⋎ ℓ ≡ ∥ V′ ∥ v′
stamp⇒⋆-security {ℓ = low} (v-l {ℓ}) ⊢l ↠V′ v′
  rewrite ℓ⋎low≡ℓ {ℓ} with ↠V′
... | _ —→⟨ r ⟩ _ = contradiction r (LVal⌿→ (v-cast (ir (inj id) (λ ()))))
... | _ ∎ with v′
... | v-cast (ir (inj id) _) = refl
stamp⇒⋆-security {ℓ = high} (v-l {low}) ⊢l ↠V′ v′ = {!!}
stamp⇒⋆-security {ℓ = high} (v-l {high}) ⊢l ↠V′ v′ = {!!}
stamp⇒⋆-security (v-cast (ir 𝓋 _)) ⊢V ↠V′ v′ = {!!}
