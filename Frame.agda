module Frame where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import CC

data Frame : Set where
  □·_ : Term → Frame

  _·□ : (V : Term) → Value V → Frame

  ref✓[_]□ : StaticLabel → Frame

  !□ : Frame

  □:=?_ : Term → Frame

  □:=✓_ : Term → Frame

  _:=✓□ : (V : Term) → Value V → Frame

  let□_ : Term → Frame

  if□ : Type → Term → Term → Frame

  □⟨_⟩ : ∀ {A B} → Cast A ⇒ B → Frame

  cast-pc_□ : Label → Frame


plug : Term → Frame → Term
plug L (□· M)          = L · M
plug M ((V ·□) v)      = V · M
plug M ref✓[ ℓ ]□      = ref✓[ ℓ ] M
plug M !□              = ! M
plug L (□:=? M)        = L :=? M
plug L (□:=✓ M)        = L :=✓ M
plug M ((V :=✓□) v)    = V :=✓ M
plug M (let□ N)        = `let M N
plug L (if□ A M N)     = if L A M N
plug M □⟨ c ⟩          = M ⟨ c ⟩
plug M (cast-pc g □)   = cast-pc g M

data Plugged : Term → Set where
  plugged-app : ∀ {L M} → Plugged (L · M)
  plugged-ref✓ : ∀ {M ℓ} → Plugged (ref✓[ ℓ ] M)
  plugged-deref : ∀ {M} → Plugged (! M)
  plugged-assign? : ∀ {L M} → Plugged (L :=? M)
  plugged-assign✓ : ∀ {L M} → Plugged (L :=✓ M)
  plugged-let : ∀ {M N} → Plugged (`let M N)
  plugged-if : ∀ {A L M N} → Plugged (if L A M N)
  plugged-cast : ∀ {A B M} {c : Cast A ⇒ B} → Plugged (M ⟨ c ⟩)
  plugged-cast-pc : ∀ {M g} → Plugged (cast-pc g M)

plug-is-plugged : ∀ M F → Plugged (plug M F)
plug-is-plugged M (□· x) = plugged-app
plug-is-plugged M ((V ·□) x) = plugged-app
plug-is-plugged M ref✓[ x ]□ = plugged-ref✓
plug-is-plugged M !□ = plugged-deref
plug-is-plugged M (□:=? x) = plugged-assign?
plug-is-plugged M (□:=✓ x) = plugged-assign✓
plug-is-plugged M ((V :=✓□) x) = plugged-assign✓
plug-is-plugged M (let□ x) = plugged-let
plug-is-plugged M (if□ x x₁ x₂) = plugged-if
plug-is-plugged M □⟨ x ⟩ = plugged-cast
plug-is-plugged M cast-pc x □ = plugged-cast-pc

plug-not-error : ∀ {e} M F → plug M F ≢ error e
plug-not-error {e} M F eq = case error-is-plugged of λ ()
  where
  error-is-plugged : Plugged (error e)
  error-is-plugged rewrite sym eq = plug-is-plugged M F

-- plug-not-● : ∀ M F → plug M F ≢ ●
-- plug-not-● M F eq = case ●-is-plugged of λ ()
--   where
--   ●-is-plugged : Plugged ●
--   ●-is-plugged rewrite sym eq = plug-is-plugged M F

plug-not-addr : ∀ {a ℓ} M F → plug M F ≢ addr a of ℓ
plug-not-addr {a} {ℓ} M F eq = case addr-is-plugged of λ ()
  where
  addr-is-plugged : Plugged (addr a of ℓ)
  addr-is-plugged rewrite sym eq = plug-is-plugged M F

plug-not-lam : ∀ {pc A N ℓ} M F → plug M F ≢ ƛ[ pc ] A ˙ N of ℓ
plug-not-lam {pc} {A} {N} {ℓ} M F eq = case lam-is-plugged of λ ()
  where
  lam-is-plugged : Plugged (ƛ[ pc ] A ˙ N of ℓ)
  lam-is-plugged rewrite sym eq = plug-is-plugged M F

plug-not-const : ∀ {ι} {k : rep ι} {ℓ} M F → plug M F ≢ $ k of ℓ
plug-not-const {ι} {k} {ℓ} M F eq = case const-is-plugged of λ ()
  where
  const-is-plugged : Plugged ($ k of ℓ)
  const-is-plugged rewrite sym eq = plug-is-plugged M F

-- plug-not-discard : ∀ {N} M F → plug M F ≢ discard N
-- plug-not-discard {N} M F eq = case discard-is-plugged of λ ()
--   where
--   discard-is-plugged : Plugged (discard N)
--   discard-is-plugged rewrite sym eq = plug-is-plugged M F
