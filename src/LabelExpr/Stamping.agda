module LabelExpr.Stamping where

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
  renaming (_∎ to _∎ₗ ; _—→⟨_⟩_ to _—→ₗ⟨_⟩_; ↠-trans to ↠-transₗ)
  hiding (Progress; progress; plug-cong)
open import CoercionExpr.SyntacComp
open import CoercionExpr.Precision renaming (prec→⊑ to precₗ→⊑)
open import CoercionExpr.SecurityLevel renaming (∥_∥ to ∥_∥ₗ)
open import CoercionExpr.Stamping
open import LabelExpr.LabelExpr



{- Normal stamping -}
stampₑ : ∀ V → LVal V → StaticLabel → LExpr
stampₑ (l ℓ)       v-l low              = l ℓ
stampₑ (l low)     v-l high             = l low ⟪ id (l low) ⨾ ↑ ⟫
stampₑ (l high)    v-l high             = l high
stampₑ (l ℓ ⟪ c̅ ⟫) (v-cast (ir 𝓋 _)) ℓ′ = l ℓ ⟪ stampₗ c̅ 𝓋 ℓ′ ⟫

{- Injective stamping -}
stamp!ₑ : ∀ V → LVal V → StaticLabel → LExpr
stamp!ₑ (l ℓ      ) v-l               ℓ′ = l ℓ ⟪ stamp!ₗ (id (l ℓ)) id ℓ′ ⟫
stamp!ₑ (l ℓ ⟪ c̅ ⟫) (v-cast (ir 𝓋 _)) ℓ′ = l ℓ ⟪ stamp!ₗ c̅ 𝓋 ℓ′ ⟫


stampₑ-wt : ∀ {V g ℓ}
  → (v : LVal V)
  → ⊢ V ⇐ g
  → ⊢ stampₑ V v ℓ ⇐ (g ⋎̃ l ℓ)
stampₑ-wt {g = g} {low} v-l ⊢V rewrite g⋎̃low≡g {g} = ⊢V
stampₑ-wt {ℓ = high} (v-l {low}) ⊢l = ⊢cast ⊢l
stampₑ-wt {ℓ = high} (v-l {high}) ⊢l = ⊢l
stampₑ-wt (v-cast (ir 𝓋 _)) (⊢cast ⊢l) = ⊢cast ⊢l

stamp!ₑ-wt : ∀ {V g ℓ}
  → (v : LVal V)
  → ⊢ V ⇐ g
  → ⊢ stamp!ₑ V v ℓ ⇐ ⋆
stamp!ₑ-wt v-l ⊢l                       = ⊢cast ⊢l
stamp!ₑ-wt (v-cast (ir _ _)) (⊢cast ⊢l) = ⊢cast ⊢l


stampₑ-LVal : ∀ {V ℓ}
  → (v : LVal V)
  → LVal (stampₑ V v ℓ)
stampₑ-LVal {V} {low} v-l = v-l
stampₑ-LVal {V} {high} (v-l {low}) = v-cast (ir (up id) (λ ()))
stampₑ-LVal {V} {high} (v-l {high}) = v-l
stampₑ-LVal {V} {ℓ} (v-cast (ir 𝓋 x)) =
  v-cast (ir (stampₗ-CVal _ 𝓋 ℓ) (stamp-not-id 𝓋 x))

stamp!ₑ-LVal : ∀ {V ℓ}
  → (v : LVal V)
  → LVal (stamp!ₑ V v ℓ)
stamp!ₑ-LVal {_} {ℓ} v-l               = v-cast (ir (stamp!ₗ-CVal _ id ℓ) (λ ()))
stamp!ₑ-LVal {V} {ℓ} (v-cast (ir 𝓋 x)) = v-cast (ir (stamp!ₗ-CVal _ 𝓋 ℓ) λ ())


-- stamp⇒⋆↠LVal : ∀ {g ℓ V}
--   → (v : LVal V)
--   → ⊢ V ⇐ g
--     ----------------------------------------------------------------------
--   → ∃[ V′ ] (stampₑ V v ℓ ⟪ coerce (g ⋎̃ l ℓ) ⇒⋆ ⟫ —↠ₑ V′) × LVal V′
-- stamp⇒⋆↠LVal {ℓ = low} (v-l {ℓ}) ⊢l rewrite ℓ⋎low≡ℓ {ℓ} =
--   ⟨ _ ⟪ _ ⟫ , _ ∎ , v-cast (ir (inj id) (λ ())) ⟩
-- stamp⇒⋆↠LVal {ℓ = high} (v-l {low}) ⊢l =
--   ⟨ _ , ♣ , v-cast (ir (inj (up id)) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (up id) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ ξ (id (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
--       _ ∎
-- stamp⇒⋆↠LVal {ℓ = high} (v-l {high}) ⊢l =
--   ⟨ _ , _ ∎ , v-cast (ir (inj id) (λ ())) ⟩
-- stamp⇒⋆↠LVal (v-cast (ir id x)) ⊢V =
--   contradiction refl (recompute (¬? (_ ==? _)) x)
-- stamp⇒⋆↠LVal {ℓ = low} (v-cast (ir (inj id) _)) (⊢cast ⊢l) =
--   ⟨ _ , ♣ , v-cast (ir (inj id) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (inj id) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ id (inj id) ⟩ _ ∎ₗ) (inj id) ⟩
--       _ ∎
-- stamp⇒⋆↠LVal {ℓ = high} (v-cast (ir (inj (id {l low})) _)) (⊢cast ⊢l) =
--   ⟨ _ , ♣ , v-cast (ir (inj (up id)) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (inj (up id)) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ id (inj (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
--       _ ∎
-- stamp⇒⋆↠LVal {ℓ = high} (v-cast (ir (inj (id {l high})) _)) (⊢cast ⊢l) =
--   ⟨ _ , ♣ , v-cast (ir (inj id) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (inj id) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ id (inj id) ⟩ _ ∎ₗ) (inj id) ⟩
--       _ ∎
-- stamp⇒⋆↠LVal {ℓ = low} (v-cast (ir (inj (up id)) _)) (⊢cast ⊢l) =
--   ⟨ _ , ♣ , v-cast (ir (inj (up id)) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (inj (up id)) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ id (inj (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
--       _ ∎
-- stamp⇒⋆↠LVal {ℓ = high} (v-cast (ir (inj (up id)) _)) (⊢cast ⊢l) =
--   ⟨ _ , ♣ , v-cast (ir (inj (up id)) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (inj (up id)) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ id (inj (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
--       _ ∎
-- stamp⇒⋆↠LVal {ℓ = low} (v-cast (ir (up id) _)) (⊢cast ⊢l) =
--   ⟨ _ , ♣ , v-cast (ir (inj (up id)) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (up id) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ ξ (id (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
--       _ ∎
-- stamp⇒⋆↠LVal {ℓ = high} (v-cast (ir (up id) _)) (⊢cast ⊢l) =
--   ⟨ _ , ♣ , v-cast (ir (inj (up id)) (λ ())) ⟩
--   where
--   ♣ = _ —→⟨ comp (ir (up id) (λ ())) ⟩
--       _ —→⟨ cast (_ —→ₗ⟨ ξ (id (up id)) ⟩ _ ∎ₗ) (inj (up id)) ⟩
--       _ ∎


stampₑ-prec : ∀ {ℓ} {V V′ g g′}
  → (v  : LVal V)
  → (v′ : LVal V′)
  → ⊢ V ⊑ V′ ⇐ g ⊑ g′
    ------------------------------------------------------------
  → ⊢ stampₑ V v ℓ ⊑ stampₑ V′ v′ ℓ ⇐ (g ⋎̃ l ℓ) ⊑ (g′ ⋎̃ l ℓ)
stampₑ-prec {low} (v-l {ℓ}) v-l ⊑-l rewrite ℓ⋎low≡ℓ {ℓ} = ⊑-l
stampₑ-prec {high} (v-l {low}) v-l ⊑-l = ⊑-cast ⊑-l (prec-refl _)
stampₑ-prec {high} (v-l {high}) v-l ⊑-l = ⊑-l
-- ⊢ ℓ ⊑ ℓ′ ⟨ c ⟩ cases are all impossible
stampₑ-prec v-l (v-cast (ir id x)) (⊑-castr ⊑-l (⊑-id l⊑l)) =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stampₑ-prec v-l (v-cast (ir (inj id) x)) (⊑-castr ⊑-l (⊑-cast _ l⊑l ()))
stampₑ-prec v-l (v-cast (ir (inj (up id)) x)) (⊑-castr ⊑-l (⊑-cast _ () _))
stampₑ-prec v-l (v-cast (ir (up id) x)) (⊑-castr ⊑-l (⊑-cast _ l⊑l ()))
stampₑ-prec {ℓ} (v-cast (ir id x)) v-l (⊑-castl ⊑-l c̅⊑ℓ′) =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stampₑ-prec {low} (v-cast (ir (inj (id {l ℓ})) _)) v-l (⊑-castl ⊑-l c̅⊑ℓ′)
  rewrite ℓ⋎low≡ℓ {ℓ} = ⊑-castl ⊑-l (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
stampₑ-prec {high} (v-cast (ir (inj (id {l low})) _)) v-l (⊑-castl ⊑-l c̅⊑ℓ′) =
  ⊑-cast ⊑-l (⊑-castl (prec-refl _) l⊑l ⋆⊑)
stampₑ-prec {high} (v-cast (ir (inj (id {l high})) _)) v-l (⊑-castl ⊑-l c̅⊑ℓ′) =
  ⊑-castl ⊑-l (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
stampₑ-prec {ℓ} (v-cast (ir (inj (up id)) _)) v-l (⊑-castl ⊑-l (⊑-cast _ () ⋆⊑))
stampₑ-prec {ℓ} (v-cast (ir (up id) _)) v-l (⊑-castl ⊑-l (⊑-cast _ l⊑l ()))
stampₑ-prec (v-cast (ir 𝓋 _ )) (v-cast (ir 𝓋′ _)) M⊑M′
  with prec→⊢ M⊑M′
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv M⊑M′
... | ⟨ refl , c̅⊑c̅′ ⟩ =
  ⊑-cast ⊑-l (stampₗ-prec 𝓋 𝓋′ c̅⊑c̅′)

stamp!ₑ-left-prec : ∀ {ℓ} {V V′ g g′}
  → (v  : LVal V)
  → (v′ : LVal V′)
  → ⊢ V ⊑ V′ ⇐ g ⊑ g′
    ------------------------------------------------------------
  → ⊢ stamp!ₑ V v ℓ ⊑ stampₑ V′ v′ ℓ ⇐ ⋆ ⊑ (g′ ⋎̃ l ℓ)
stamp!ₑ-left-prec {low} (v-l {ℓ}) v-l ⊑-l rewrite ℓ⋎low≡ℓ {ℓ} = ⊑-castl ⊑-l (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
stamp!ₑ-left-prec {high} (v-l {low}) v-l ⊑-l = ⊑-cast ⊑-l ↑!⊑↑
stamp!ₑ-left-prec {high} (v-l {high}) v-l ⊑-l = ⊑-castl ⊑-l (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
-- ⊢ ℓ ⊑ ℓ′ ⟨ c ⟩ cases are all impossible
stamp!ₑ-left-prec v-l (v-cast (ir id x)) (⊑-castr ⊑-l (⊑-id l⊑l)) =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stamp!ₑ-left-prec v-l (v-cast (ir (inj id) x)) (⊑-castr ⊑-l (⊑-cast _ l⊑l ()))
stamp!ₑ-left-prec v-l (v-cast (ir (inj (up id)) x)) (⊑-castr ⊑-l (⊑-cast _ () _))
stamp!ₑ-left-prec v-l (v-cast (ir (up id) x)) (⊑-castr ⊑-l (⊑-cast _ l⊑l ()))
stamp!ₑ-left-prec {ℓ} (v-cast (ir id x)) v-l (⊑-castl ⊑-l c̅⊑ℓ′) =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stamp!ₑ-left-prec {low} (v-cast (ir (inj (id {l ℓ})) _)) v-l (⊑-castl ⊑-l c̅⊑ℓ′)
  rewrite ℓ⋎low≡ℓ {ℓ} = ⊑-castl ⊑-l (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
stamp!ₑ-left-prec {high} (v-cast (ir (inj (id {l low})) _)) v-l (⊑-castl ⊑-l c̅⊑ℓ′) =
  ⊑-cast ⊑-l (⊑-castl (prec-refl _) l⊑l ⋆⊑)
stamp!ₑ-left-prec {high} (v-cast (ir (inj (id {l high})) _)) v-l (⊑-castl ⊑-l c̅⊑ℓ′) =
  ⊑-castl ⊑-l (⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑)
stamp!ₑ-left-prec {ℓ} (v-cast (ir (inj (up id)) _)) v-l (⊑-castl ⊑-l (⊑-cast _ () ⋆⊑))
stamp!ₑ-left-prec {ℓ} (v-cast (ir (up id) _)) v-l (⊑-castl ⊑-l (⊑-cast _ l⊑l ()))
stamp!ₑ-left-prec (v-cast (ir 𝓋 _ )) (v-cast (ir 𝓋′ _)) M⊑M′
  with prec→⊢ M⊑M′
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv M⊑M′
... | ⟨ refl , c̅⊑c̅′ ⟩ = ⊑-cast ⊑-l (stamp!ₗ-left-prec 𝓋 𝓋′ c̅⊑c̅′ ≼-refl)

stamp!ₑ-prec : ∀ {ℓ ℓ′} {V V′ g g′}
  → (v  : LVal V)
  → (v′ : LVal V′)
  → ⊢ V ⊑ V′ ⇐ g ⊑ g′
  → ℓ ≼ ℓ′
    ------------------------------------------------------------
  → ⊢ stamp!ₑ V v ℓ ⊑ stamp!ₑ V′ v′ ℓ′ ⇐ ⋆ ⊑ ⋆
stamp!ₑ-prec v-l v-l ⊑-l ℓ≼ℓ′ = ⊑-cast ⊑-l (stamp!ₗ-prec id id (⊑-id l⊑l) ℓ≼ℓ′)
stamp!ₑ-prec v-l (v-cast (ir id _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼l = ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec v-l (v-cast (ir (inj id) _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼l = ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec v-l (v-cast (ir (inj (up id)) _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼l = ⊑-cast ⊑-l !⊑↑!
stamp!ₑ-prec v-l (v-cast (ir (up id) _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼l = ⊑-cast ⊑-l !⊑↑!
stamp!ₑ-prec v-l (v-cast (ir id x)) (⊑-castr ⊑-l ℓ⊑c̅) l≼h =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stamp!ₑ-prec (v-l {high}) (v-cast (ir (inj id) _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼h =
  ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec (v-l {low}) (v-cast (ir (inj id) _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼h = ⊑-cast ⊑-l !⊑↑!
stamp!ₑ-prec v-l (v-cast (ir (inj (up id)) _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼h = ⊑-cast ⊑-l !⊑↑!
stamp!ₑ-prec v-l (v-cast (ir (up id) _)) (⊑-castr ⊑-l ℓ⊑c̅) l≼h = ⊑-cast ⊑-l !⊑↑!
stamp!ₑ-prec v-l (v-cast (ir id x)) (⊑-castr ⊑-l ℓ⊑c̅) h≼h =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stamp!ₑ-prec (v-l {high}) (v-cast (ir (inj id) _)) (⊑-castr ⊑-l ℓ⊑c̅) h≼h =
  ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec (v-l {low}) (v-cast (ir (inj id) _)) (⊑-castr ⊑-l ℓ⊑c̅) h≼h =
  ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec v-l (v-cast (ir (inj (up id)) _)) (⊑-castr ⊑-l (⊑-cast _ () _)) h≼h
stamp!ₑ-prec v-l (v-cast (ir (up id) _)) (⊑-castr ⊑-l (⊑-cast _ _ ())) h≼h
stamp!ₑ-prec (v-cast (ir id x)) v-l (⊑-castl ⊑-l _) ℓ≼ℓ′ =
  contradiction refl (recompute (¬? (_ ==? _)) x)
stamp!ₑ-prec (v-cast (ir (inj id) _)) (v-l {ℓ}) (⊑-castl ⊑-l x) l≼l = ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec (v-cast {high} (ir (inj id) _)) (v-l {.high}) (⊑-castl ⊑-l x) l≼h =
  ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec (v-cast {low} (ir (inj id) _)) (v-l {.low}) (⊑-castl ⊑-l x) l≼h =
  ⊑-cast ⊑-l !⊑↑!
stamp!ₑ-prec (v-cast {high} (ir (inj id) _)) (v-l {.high}) (⊑-castl ⊑-l x) h≼h = ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec (v-cast {low} (ir (inj id) _)) (v-l {.low}) (⊑-castl ⊑-l x) h≼h = ⊑-cast ⊑-l (prec-refl _)
stamp!ₑ-prec (v-cast (ir (inj (up id)) _)) v-l (⊑-castl V⊑V′ (⊑-cast (⊑-cast x l⊑l ()) _ _))
stamp!ₑ-prec (v-cast (ir (up id) _)) v-l (⊑-castl V⊑V′ (⊑-cast x l⊑l ()))
stamp!ₑ-prec (v-cast (ir v _)) (v-cast (ir v′ _)) V⊑V′ ℓ≼ℓ′
  with prec→⊢ V⊑V′
... | ⟨ ⊢cast ⊢l , ⊢cast ⊢l ⟩
  with prec-inv V⊑V′
... | ⟨ refl , c̅⊑c̅′ ⟩ =
  ⊑-cast ⊑-l (stamp!ₗ-prec v v′ c̅⊑c̅′ ℓ≼ℓ′)
