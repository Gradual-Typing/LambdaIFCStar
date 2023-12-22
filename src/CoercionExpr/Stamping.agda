module CoercionExpr.Stamping where

open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
open import CoercionExpr.SecurityLevel
open import CoercionExpr.Precision


{-
  Stamping on coercions in normal form:
    1) stamps the target type of the coercion and
    2) promotes the coercion's security by ℓ′
  -}
stampₗ : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → CVal c̅ → (ℓ′ : StaticLabel)
  → CExpr l ℓ ⇒ (g ⋎̃ l ℓ′)
stampₗ {g = g} c̅                  v             low  rewrite g⋎̃low≡g {g} = c̅
stampₗ (id (l low))               id            high = id (l low) ⨾ ↑
stampₗ (id (l high))              id            high = id (l high)
stampₗ (id (l low) ⨾ low !)       (inj id)      high = id (l low) ⨾ ↑ ⨾ high !
stampₗ (id (l high) ⨾ high !)     (inj id)      high = id (l high) ⨾ high !
stampₗ (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = id (l low) ⨾ ↑ ⨾ high !
stampₗ (id (l low) ⨾ ↑)          (up id)       high = id (l low) ⨾ ↑

{-
  Stamping with injection:
    1) returns an injected coercion whose security is promoted by ℓ′
    2) allows different security levels on less precise and more precise sides
  -}
stamp!ₗ : ∀ {ℓ g} → (c̅ : CExpr l ℓ ⇒ g) → CVal c̅ → (ℓ′ : StaticLabel)
  → CExpr l ℓ ⇒ ⋆
stamp!ₗ {ℓ}  {⋆}    c̅              v             low  = c̅
stamp!ₗ {ℓ₁} {l ℓ₂} c̅              v             low  = c̅ ⨾ ℓ₂ !
stamp!ₗ (id (l low))               id            high = id (l low) ⨾ ↑ ⨾ high !
stamp!ₗ (id (l high))              id            high = id (l high) ⨾ high !
stamp!ₗ (id (l low) ⨾ low !)       (inj id)      high = id (l low) ⨾ ↑ ⨾ high !
stamp!ₗ (id (l high) ⨾ high !)     (inj id)      high = id (l high) ⨾ high !
stamp!ₗ (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = id (l low) ⨾ ↑ ⨾ high !
stamp!ₗ (id (l low) ⨾ ↑)          (up id)       high = id (l low) ⨾ ↑ ⨾ high !


{- Both variants of stamping return coercions in normal form -}
stampₗ-CVal : ∀ {ℓ g} (c̅ : CExpr l ℓ ⇒ g)
  → (v : CVal c̅)
  → (ℓ′ : StaticLabel)
  → CVal (stampₗ c̅ v ℓ′)
stamp!ₗ-CVal : ∀ {ℓ g} (c̅ : CExpr l ℓ ⇒ g)
  → (v : CVal c̅)
  → (ℓ′ : StaticLabel)
  → CVal (stamp!ₗ c̅ v ℓ′)
stampₗ-CVal {g = g} c̅ v low rewrite g⋎̃low≡g {g} = v
stampₗ-CVal (id (l low)) id high = up id
stampₗ-CVal (id (l high)) id high = id
stampₗ-CVal (id (l low) ⨾ low !) (inj id) high = inj (up id)
stampₗ-CVal (id (l high) ⨾ high !) (inj id) high = inj id
stampₗ-CVal (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = inj (up id)
stampₗ-CVal (id (l low) ⨾ ↑) (up id) high = up id
stamp!ₗ-CVal {g = ⋆} c̅ v low = v
stamp!ₗ-CVal {g = l _} c̅ v low = inj v
stamp!ₗ-CVal (id (l low)) id high = inj (up id)
stamp!ₗ-CVal (id (l high)) id high = inj id
stamp!ₗ-CVal (id (l low) ⨾ low !) (inj id) high = inj (up id)
stamp!ₗ-CVal (id (l high) ⨾ high !) (inj id) high = inj id
stamp!ₗ-CVal (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = inj (up id)
stamp!ₗ-CVal (id (l low) ⨾ ↑) (up id) high = inj (up id)

stampₗ-low : ∀ {ℓ g} {c̅ : CExpr l ℓ ⇒ g}
  → (𝓋 : CVal c̅)
  → subst (λ □ → CExpr l ℓ ⇒ □) g⋎̃low≡g (stampₗ c̅ 𝓋 low) ≡ c̅
stampₗ-low (id {l low}) = refl
stampₗ-low (id {l high}) = refl
stampₗ-low (inj id) = refl
stampₗ-low (inj (up id)) = refl
stampₗ-low (up id) = refl

stamp-not-id : ∀ {ℓ ℓ′ g} {c̅ : CExpr l ℓ ⇒ g}
  → CVal c̅
  → l ℓ ≢ g
  → l ℓ ≢ g ⋎̃ l ℓ′
stamp-not-id {low} {low} id neq = neq
stamp-not-id {low} {high} id neq = λ ()
stamp-not-id {high} id neq = neq
stamp-not-id (inj id) neq = neq
stamp-not-id (inj (up id)) neq = neq
stamp-not-id (up id) neq = neq



{- **** Properties of stamping about security **** -}

{- Both stamping functions promote the coercion's security by ℓ′ -}
stampₗ-security : ∀ {ℓ g}
  → (c̅ : CExpr l ℓ ⇒ g)
  → (v : CVal c̅)
  → (ℓ′ : StaticLabel)
    ---------------------------------------------------------
  → (∥ c̅ ∥ v) ⋎ ℓ′ ≡ ∥ stampₗ c̅ v ℓ′ ∥ (stampₗ-CVal c̅ v ℓ′)
stampₗ-security {g = g} c̅ v low
  rewrite g⋎̃low≡g {g} | ℓ⋎low≡ℓ {∥ c̅ ∥ v} = refl
stampₗ-security (id (l low)) id high = refl
stampₗ-security (id (l high)) id high = refl
stampₗ-security (id (l low) ⨾ low !) (inj id) high = refl
stampₗ-security (id (l high) ⨾ high !) (inj id) high = refl
stampₗ-security (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = refl
stampₗ-security (id (l low) ⨾ ↑) (up id) high = refl

stamp!ₗ-security : ∀ {ℓ g}
  → (c̅ : CExpr l ℓ ⇒ g)
  → (v : CVal c̅)
  → (ℓ′ : StaticLabel)
    ---------------------------------------------------------
  → (∥ c̅ ∥ v) ⋎ ℓ′ ≡ ∥ stamp!ₗ c̅ v ℓ′ ∥ (stamp!ₗ-CVal c̅ v ℓ′)
stamp!ₗ-security {g = ⋆} c̅ v low rewrite ℓ⋎low≡ℓ {∥ c̅ ∥ v} = refl
stamp!ₗ-security {g = l ℓ} c̅ id low rewrite ℓ⋎low≡ℓ {ℓ} = refl
stamp!ₗ-security {g = l high} c̅ (up id) low = refl
stamp!ₗ-security (id (l low)) id high = refl
stamp!ₗ-security (id (l high)) id high = refl
stamp!ₗ-security (id (l low) ⨾ low !) (inj id) high = refl
stamp!ₗ-security (id (l high) ⨾ high !) (inj id) high = refl
stamp!ₗ-security (id (l low) ⨾ ↑ ⨾ high !) (inj (up id)) high = refl
stamp!ₗ-security (id (l low) ⨾ ↑) (up id) high = refl


{- **** Properties of stamping about precision **** -}

{- Stamping preserves precision when the left side is an injection -}
stamp⋆ₗ-prec : ∀ {ℓ ℓ₁ ℓ₂ g} {c̅ : CExpr l ℓ ⇒ ⋆} {d̅ : CExpr l ℓ ⇒ g}
  → (v : CVal c̅)
  → (v′ : CVal d̅)
  → ⊢ c̅ ⊑ d̅
  → ℓ₁ ≼ ℓ₂
    ------------------------------------
  → ⊢ stampₗ c̅ v ℓ₁ ⊑ stampₗ d̅ v′ ℓ₂
stamp⋆ₗ-prec {low} (inj id) id prec l≼l = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp⋆ₗ-prec {high} (inj id) id prec l≼l = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp⋆ₗ-prec {low} (inj id) id (⊑-castl prec l⊑l x₁) l≼h = !⊑↑
stamp⋆ₗ-prec {high} (inj id) id (⊑-castl prec l⊑l x₁) l≼h = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp⋆ₗ-prec {low} (inj id) id (⊑-castl prec l⊑l x₁) h≼h = ↑!⊑↑
stamp⋆ₗ-prec {high} (inj id) id (⊑-castl prec l⊑l x₁) h≼h = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp⋆ₗ-prec (inj id) (inj id) prec l≼l = prec-refl _
stamp⋆ₗ-prec {low} (inj id) (inj id) prec l≼h = !⊑↑!
stamp⋆ₗ-prec {high} (inj id) (inj id) prec l≼h = prec-refl _
stamp⋆ₗ-prec (inj (id {l low})) (inj id) prec h≼h = prec-refl _
stamp⋆ₗ-prec (inj (id {l high})) (inj id) prec h≼h = prec
stamp⋆ₗ-prec (inj id) (inj (up id)) prec l≼l = !⊑↑!
stamp⋆ₗ-prec (inj id) (inj (up id)) prec l≼h = !⊑↑!
stamp⋆ₗ-prec (inj id) (inj (up id)) prec h≼h = prec-refl _
-- ⊢ id low ; low ! ⊑ id low ; ↑
stamp⋆ₗ-prec (inj id) (up id) prec l≼l = !⊑↑
stamp⋆ₗ-prec (inj id) (up id) prec l≼h = !⊑↑
stamp⋆ₗ-prec (inj id) (up id) prec h≼h = ↑!⊑↑
stamp⋆ₗ-prec (inj (up id)) id (⊑-castl prec () _) leq
stamp⋆ₗ-prec (inj (up id)) (inj id) (⊑-castr (⊑-castl prec () _) _ _) leq
stamp⋆ₗ-prec (inj (up id)) (inj (up id)) prec l≼l = prec-refl _
stamp⋆ₗ-prec (inj (up id)) (inj (up id)) prec l≼h = prec-refl _
stamp⋆ₗ-prec (inj (up id)) (inj (up id)) prec h≼h = prec-refl _
-- ⊢ id low ; ↑ ; high ! ⊑ id low ; ↑
stamp⋆ₗ-prec (inj (up id)) (up id) prec l≼l = ↑!⊑↑
stamp⋆ₗ-prec (inj (up id)) (up id) prec l≼h = ↑!⊑↑
stamp⋆ₗ-prec (inj (up id)) (up id) prec h≼h = ↑!⊑↑


{- Stamping with the same security label preserves precision -}
stampₗ-prec : ∀ {ℓ ℓ₁ g₁ g₂} {c̅ : CExpr l ℓ₁ ⇒ g₁} {d̅ : CExpr l ℓ₁ ⇒ g₂}
  → (v : CVal c̅)
  → (v′ : CVal d̅)
  → ⊢ c̅ ⊑ d̅
    ------------------------------------
  → ⊢ stampₗ c̅ v ℓ ⊑ stampₗ d̅ v′ ℓ
stampₗ-prec id id (⊑-id l⊑l) = prec-refl _
stampₗ-prec id (inj id) (⊑-castr _ l⊑l ())
stampₗ-prec id (up id) (⊑-castr _ l⊑l ())
stampₗ-prec (up id) id (⊑-castl _ l⊑l ())
stampₗ-prec (up id) (inj id) (⊑-cast _ _ ())
stampₗ-prec (up id) (inj id) (⊑-castl _ () _)
stampₗ-prec (up id) (inj id) (⊑-castr _ _ ())
stampₗ-prec (up id) (inj (up id)) (⊑-cast _ _ ())
stampₗ-prec (up id) (inj (up id)) (⊑-castl _ () _)
stampₗ-prec (up id) (inj (up id)) (⊑-castr _ _ ())
stampₗ-prec (up id) (up id) c̅⊑d̅ = prec-refl _
stampₗ-prec {ℓ} (inj v₁) v₂ prec = stamp⋆ₗ-prec {ℓ₁ = ℓ} (inj v₁) v₂ prec ≼-refl


stamp!ₗ-left-prec : ∀ {ℓ ℓ₁ ℓ₂ g₁ g₂} {c̅ : CExpr l ℓ ⇒ g₁} {d̅ : CExpr l ℓ ⇒ g₂}
  → (v : CVal c̅)
  → (v′ : CVal d̅)
  → ⊢ c̅ ⊑ d̅
  → ℓ₁ ≼ ℓ₂
    ------------------------------------
  → ⊢ stamp!ₗ c̅ v ℓ₁ ⊑ stampₗ d̅ v′ ℓ₂
stamp!ₗ-left-prec (id {l low}) id (⊑-id l⊑l) l≼l = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec (id {l high}) id (⊑-id l⊑l) l≼l = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec {low} id id (⊑-id l⊑l) l≼h = !⊑↑
stamp!ₗ-left-prec {high} id id (⊑-id l⊑l) l≼h = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec (id {l low}) id (⊑-id l⊑l) h≼h = ↑!⊑↑
stamp!ₗ-left-prec (id {l high}) id (⊑-id l⊑l) h≼h = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec id (inj id) (⊑-castr _ l⊑l ()) _
stamp!ₗ-left-prec id (up id) (⊑-castr _ l⊑l ()) _
stamp!ₗ-left-prec {low} (inj id) id prec l≼l = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec {high} (inj id) id prec l≼l = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec {low} (inj id) id (⊑-castl prec l⊑l x₁) l≼h = !⊑↑
stamp!ₗ-left-prec {high} (inj id) id (⊑-castl prec l⊑l x₁) l≼h = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec {low} (inj id) id (⊑-castl prec l⊑l x₁) h≼h = ↑!⊑↑
stamp!ₗ-left-prec {high} (inj id) id (⊑-castl prec l⊑l x₁) h≼h = ⊑-castl (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ-left-prec (inj id) (inj id) prec l≼l = prec-refl _
stamp!ₗ-left-prec {low} (inj id) (inj id) prec l≼h = !⊑↑!
stamp!ₗ-left-prec {high} (inj id) (inj id) prec l≼h = prec-refl _
stamp!ₗ-left-prec (inj (id {l low})) (inj id) prec h≼h = prec-refl _
stamp!ₗ-left-prec (inj (id {l high})) (inj id) prec h≼h = prec
stamp!ₗ-left-prec (inj id) (inj (up id)) prec l≼l = !⊑↑!
stamp!ₗ-left-prec (inj id) (inj (up id)) prec l≼h = !⊑↑!
stamp!ₗ-left-prec (inj id) (inj (up id)) prec h≼h = prec-refl _
stamp!ₗ-left-prec (inj id) (up id) prec l≼l = !⊑↑
stamp!ₗ-left-prec (inj id) (up id) prec l≼h = !⊑↑
stamp!ₗ-left-prec (inj id) (up id) prec h≼h = ↑!⊑↑
stamp!ₗ-left-prec (inj (up id)) id (⊑-castl prec () _) leq
stamp!ₗ-left-prec (inj (up id)) (inj id) (⊑-castr (⊑-castl prec () _) _ _) leq
stamp!ₗ-left-prec (inj (up id)) (inj (up id)) prec l≼l = prec-refl _
stamp!ₗ-left-prec (inj (up id)) (inj (up id)) prec l≼h = prec-refl _
stamp!ₗ-left-prec (inj (up id)) (inj (up id)) prec h≼h = prec-refl _
stamp!ₗ-left-prec (inj (up id)) (up id) prec l≼l = ↑!⊑↑
stamp!ₗ-left-prec (inj (up id)) (up id) prec l≼h = ↑!⊑↑
stamp!ₗ-left-prec (inj (up id)) (up id) prec h≼h = ↑!⊑↑
stamp!ₗ-left-prec (up id) id (⊑-castl prec _ ()) leq
stamp!ₗ-left-prec (up id) (inj id) (⊑-cast prec _ ()) leq
stamp!ₗ-left-prec (up id) (inj id) (⊑-castl prec _ ()) leq
stamp!ₗ-left-prec (up id) (inj id) (⊑-castr prec () _) leq
stamp!ₗ-left-prec (up id) (inj (up id)) prec l≼l = prec-refl _
stamp!ₗ-left-prec (up id) (inj (up id)) prec l≼h = prec-refl _
stamp!ₗ-left-prec (up id) (inj (up id)) prec h≼h = prec-refl _
stamp!ₗ-left-prec (up id) (up id) prec l≼l = ↑!⊑↑
stamp!ₗ-left-prec (up id) (up id) prec l≼h = ↑!⊑↑
stamp!ₗ-left-prec (up id) (up id) prec h≼h = ↑!⊑↑


stamp!ₗ-prec : ∀ {ℓ ℓ₁ ℓ₂ g₁ g₂} {c̅ : CExpr l ℓ ⇒ g₁} {d̅ : CExpr l ℓ ⇒ g₂}
  → (v  : CVal c̅)
  → (v′ : CVal d̅)
  → ⊢ c̅ ⊑ d̅
  → ℓ₁ ≼ ℓ₂
    ---------------------------------------
  → ⊢ stamp!ₗ c̅ v ℓ₁ ⊑ stamp!ₗ d̅ v′ ℓ₂
stamp!ₗ-prec id id (⊑-id l⊑l) l≼l = prec-refl _
stamp!ₗ-prec {low} id id (⊑-id l⊑l) l≼h = !⊑↑!
stamp!ₗ-prec {high} id id (⊑-id l⊑l) l≼h = prec-refl _
stamp!ₗ-prec id id (⊑-id l⊑l) h≼h = prec-refl _
stamp!ₗ-prec id (inj id) (⊑-castr _ l⊑l ()) _
stamp!ₗ-prec id (up id) (⊑-castr _ l⊑l ()) _
stamp!ₗ-prec {low} (inj id) id prec l≼l = ⊑-castr prec ⋆⊑ ⋆⊑
stamp!ₗ-prec {high} (inj id) id prec l≼l = ⊑-castr prec ⋆⊑ ⋆⊑
stamp!ₗ-prec {low} (inj id) id (⊑-castl prec l⊑l x₁) l≼h = !⊑↑!
stamp!ₗ-prec {high} (inj id) id (⊑-castl prec l⊑l x₁) l≼h = prec-refl _
stamp!ₗ-prec {low} (inj id) id (⊑-castl prec l⊑l x₁) h≼h = prec-refl _
stamp!ₗ-prec {high} (inj id) id (⊑-castl prec l⊑l x₁) h≼h = prec-refl _
stamp!ₗ-prec (inj id) (inj id) prec l≼l = prec-refl _
stamp!ₗ-prec {low} (inj id) (inj id) prec l≼h = !⊑↑!
stamp!ₗ-prec {high} (inj id) (inj id) prec l≼h = prec-refl _
stamp!ₗ-prec (inj id) (inj id) prec h≼h = prec-refl _
stamp!ₗ-prec (inj id) (inj (up id)) prec l≼l = !⊑↑!
stamp!ₗ-prec (inj id) (inj (up id)) prec l≼h = !⊑↑!
stamp!ₗ-prec (inj id) (inj (up id)) prec h≼h = prec-refl _
stamp!ₗ-prec (inj id) (up id) prec l≼l = !⊑↑!
stamp!ₗ-prec (inj id) (up id) prec l≼h = !⊑↑!
stamp!ₗ-prec (inj id) (up id) prec h≼h = prec-refl _
stamp!ₗ-prec (inj (up id)) id (⊑-castl prec () _) leq
stamp!ₗ-prec (inj (up id)) (inj id) (⊑-castr (⊑-castl prec () _) _ _) leq
stamp!ₗ-prec (inj (up id)) (inj (up id)) prec l≼l = prec-refl _
stamp!ₗ-prec (inj (up id)) (inj (up id)) prec l≼h = prec-refl _
stamp!ₗ-prec (inj (up id)) (inj (up id)) prec h≼h = prec-refl _
stamp!ₗ-prec (inj (up id)) (up id) prec l≼l = prec-refl _
stamp!ₗ-prec (inj (up id)) (up id) prec l≼h = prec-refl _
stamp!ₗ-prec (inj (up id)) (up id) prec h≼h = prec-refl _
stamp!ₗ-prec (up id) id (⊑-castl prec _ ()) leq
stamp!ₗ-prec (up id) (inj id) (⊑-cast prec _ ()) leq
stamp!ₗ-prec (up id) (inj id) (⊑-castl prec _ ()) leq
stamp!ₗ-prec (up id) (inj id) (⊑-castr prec () _) leq
stamp!ₗ-prec (up id) (inj (up id)) prec l≼l = prec-refl _
stamp!ₗ-prec (up id) (inj (up id)) prec l≼h = prec-refl _
stamp!ₗ-prec (up id) (inj (up id)) prec h≼h = prec-refl _
stamp!ₗ-prec (up id) (up id) prec l≼l = prec-refl _
stamp!ₗ-prec (up id) (up id) prec l≼h = prec-refl _
stamp!ₗ-prec (up id) (up id) prec h≼h = prec-refl _


stamp⋆ₗ⊑↑ : ∀ {ℓ} (c̅ : CExpr l low ⇒ ⋆)
  → (𝓋 : CVal c̅)
  → ⊢ stampₗ c̅ 𝓋 ℓ ⊑ id (l low) ⨾ ↑
stamp⋆ₗ⊑↑ {ℓ = high} (id .(l low) ⨾ (_ !)) (inj id) = ↑!⊑↑
stamp⋆ₗ⊑↑ {ℓ = low} (id .(l low) ⨾ (_ !)) (inj id) = !⊑↑
stamp⋆ₗ⊑↑ {ℓ = high} (id .(l low) ⨾ ↑ ⨾ (_ !)) (inj (up id)) = ↑!⊑↑
stamp⋆ₗ⊑↑ {ℓ = low} (id .(l low) ⨾ ↑ ⨾ (_ !)) (inj (up id)) = ↑!⊑↑

stamp!ₗ⊑↑ : ∀ {g ℓ} (c̅ : CExpr l low ⇒ g)
  → (𝓋 : CVal c̅)
  → ⊢ stamp!ₗ c̅ 𝓋 ℓ ⊑ id (l low) ⨾ ↑
stamp!ₗ⊑↑ {ℓ = high} (id .(l low)) id = ↑!⊑↑
stamp!ₗ⊑↑ {ℓ = low} (id .(l low)) id = !⊑↑
stamp!ₗ⊑↑ {ℓ = high} (id .(l low) ⨾ (_ !)) (inj id) = ↑!⊑↑
stamp!ₗ⊑↑ {ℓ = low} (id .(l low) ⨾ (_ !)) (inj id) = !⊑↑
stamp!ₗ⊑↑ {ℓ = high} (id .(l low) ⨾ ↑ ⨾ (_ !)) (inj (up id)) = ↑!⊑↑
stamp!ₗ⊑↑ {ℓ = low} (id .(l low) ⨾ ↑ ⨾ (_ !)) (inj (up id)) = ↑!⊑↑
stamp!ₗ⊑↑ {ℓ = high} (id .(l low) ⨾ ↑) (up id) = ↑!⊑↑
stamp!ₗ⊑↑ {ℓ = low} (id .(l low) ⨾ ↑) (up id) = ↑!⊑↑

stamp⋆ₗ⊑ℓ : ∀ {ℓ ℓ′} (c̅ : CExpr l ℓ ⇒ ⋆)
  → ⊢l c̅ ⊑ l ℓ
  → (𝓋 : CVal c̅)
  → ℓ′ ≼ ℓ
  → ⊢l stampₗ c̅ 𝓋 ℓ′ ⊑ l ℓ
stamp⋆ₗ⊑ℓ (id (l low) ⨾ _ !) c̅⊑ℓ (inj id) l≼l = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp⋆ₗ⊑ℓ (id (l high) ⨾ _ !) c̅⊑ℓ (inj id) l≼h = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp⋆ₗ⊑ℓ (id (l high) ⨾ _ !) c̅⊑ℓ (inj id) h≼h = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp⋆ₗ⊑ℓ (id (l low) ⨾ ↑ ⨾ _ !) (⊑-cast _ () _) (inj (up id)) l≼l

stamp!ₗ⊑ℓ : ∀ {g ℓ ℓ′} (c̅ : CExpr l ℓ ⇒ g)
  → ⊢l c̅ ⊑ l ℓ
  → (𝓋 : CVal c̅)
  → ℓ′ ≼ ℓ
  → ⊢l stamp!ₗ c̅ 𝓋 ℓ′ ⊑ l ℓ
stamp!ₗ⊑ℓ (id (l low)) c̅⊑ℓ id l≼l = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ⊑ℓ (id (l high)) c̅⊑ℓ id l≼h = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ⊑ℓ (id (l high)) c̅⊑ℓ id h≼h = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ⊑ℓ (id (l low) ⨾ _ !) c̅⊑ℓ (inj id) l≼l = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ⊑ℓ (id (l high) ⨾ _ !) c̅⊑ℓ (inj id) l≼h = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ⊑ℓ (id (l high) ⨾ _ !) c̅⊑ℓ (inj id) h≼h = ⊑-cast (⊑-id l⊑l) l⊑l ⋆⊑
stamp!ₗ⊑ℓ (id (l low) ⨾ ↑ ⨾ _ !) (⊑-cast _ () _) (inj (up id)) l≼l
stamp!ₗ⊑ℓ (id .(l low) ⨾ ↑) (⊑-cast _ _ ()) (up id)
