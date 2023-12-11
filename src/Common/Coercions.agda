{- Coercions on terms -}

module Common.Coercions where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Function using (case_of_; case_return_of_)

open import Common.Utils
open import Common.Types
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
  hiding   (Progress; progress)
  renaming (_—→⟨_⟩_ to _—→ₗ⟨_⟩_; _∎ to _∎ₗ ;
            _—→_ to _—→ₗ_; _—↠_ to _—↠ₗ_;
            plug-cong to plug-congₗ)
  public
open import CoercionExpr.SecurityLevel renaming (∥_∥ to ∥_∥ₗ) public
open import CoercionExpr.Stamping
open import CoercionExpr.SyntacComp renaming (_⨟_ to _⊹⊹_)


infix 6 Castᵣ_⇒_
infix 6 Cast_⇒_

data Castᵣ_⇒_ : RawType → RawType → Set
data Cast_⇒_  : Type → Type → Set

data Castᵣ_⇒_ where

  id  : ∀ ι → Castᵣ ` ι ⇒ ` ι

  ref : ∀ {A B}
    → (c : Cast B ⇒ A)  {- in  -}
    → (d : Cast A ⇒ B)  {- out -}
    → Castᵣ Ref A ⇒ Ref B

  fun : ∀ {g₁ g₂} {A B C D}
    → CExpr g₂ ⇒ g₁
    → (c : Cast C ⇒ A)  {- in  -}
    → (d : Cast B ⇒ D)  {- out -}
    → Castᵣ ⟦ g₁ ⟧ A ⇒ B ⇒ ⟦ g₂ ⟧ C ⇒ D


data Cast_⇒_ where
  cast : ∀ {S T g₁ g₂}
    → Castᵣ S ⇒ T
    → CExpr g₁ ⇒ g₂
    → Cast S of g₁ ⇒ T of g₂


{- Irreducible coercions form values -}
data Irreducible : ∀ {A B} → Cast A ⇒ B → Set where
  ir-base : ∀ {ι ℓ g} {c̅ : CExpr l ℓ ⇒ g}
    → CVal c̅
    → l ℓ ≢ g  {- c̅ ≢ id -}
    → Irreducible (cast (id ι) c̅)

  ir-ref : ∀ {A B ℓ g}
      {c : Cast B ⇒ A} {d : Cast A ⇒ B} {c̅ : CExpr l ℓ ⇒ g}
    → CVal c̅
    → Irreducible (cast (ref c d) c̅)

  ir-fun : ∀ {A B C D ℓ g gᶜ₁ gᶜ₂}
      {c : Cast C ⇒ A} {d : Cast B ⇒ D}
      {c̅ : CExpr l ℓ ⇒ g} {d̅ : CExpr gᶜ₁ ⇒ gᶜ₂}
    → CVal c̅
    → Irreducible (cast (fun d̅ c d) c̅)


coerceᵣ : ∀ {S T} → S ≲ᵣ T → BlameLabel → Castᵣ S ⇒ T
coerce : ∀ {A B} → A ≲ B → BlameLabel → Cast A ⇒ B

coerceᵣ {` ι} {` ι} ≲-ι p = id ι
coerceᵣ {Ref A} {Ref B} (≲-ref A≲B B≲A) p =
  ref (coerce B≲A p) (coerce A≲B p)
coerceᵣ {⟦ g₁ ⟧ A ⇒ B} {⟦ g₂ ⟧ C ⇒ D} (≲-fun g₂≾g₁ C≲A B≲D) p =
  fun (coerceₗ g₂≾g₁ p) (coerce C≲A p) (coerce B≲D p)

coerce {S of g₁} {T of g₂} (≲-ty g₁≾g₂ S≲T) p =
  cast (coerceᵣ S≲T p) (coerceₗ g₁≾g₂ p)


coerceᵣ-id : ∀ T → Castᵣ T ⇒ T
coerce-id : ∀ A → Cast A ⇒ A

coerceᵣ-id (` ι) = id ι
coerceᵣ-id (Ref A) = ref (coerce-id A) (coerce-id A)
coerceᵣ-id (⟦ g ⟧ A ⇒ B) = fun (id g) (coerce-id A) (coerce-id B)

coerce-id (T of g) = cast (coerceᵣ-id T) (id g)


-- used in compilation
coerce-<:ᵣ : ∀ {S T} → S <:ᵣ T → Castᵣ S ⇒ T
coerce-<:  : ∀ {A B} → A <:  B → Cast  A ⇒ B

coerce-<:ᵣ {` ι} {` ι} <:-ι = id ι
coerce-<:ᵣ {Ref A} {Ref B} (<:-ref A<:B B<:A) =
  ref (coerce-<: B<:A) (coerce-<: A<:B)
coerce-<:ᵣ {⟦ g₁ ⟧ A ⇒ B} {⟦ g₂ ⟧ C ⇒ D} (<:-fun g₂<:g₁ C<:A B<:D) =
  fun (coerce-<:ₗ g₂<:g₁) (coerce-<: C<:A) (coerce-<: B<:D)
coerce-<: (<:-ty g₁<:g₂ S<:T) = cast (coerce-<:ᵣ S<:T) (coerce-<:ₗ g₁<:g₂)


inject : ∀ T g → Cast T of g ⇒ T of ⋆
inject T g = cast (coerceᵣ-id T) (coerce g ⇒⋆)

-- note that the coercion in PC position can be a projection
fun-to-⋆ : ∀ g₁ A T g₂ g₃ → (p : BlameLabel) → Cast (⟦ g₁ ⟧ A ⇒ (T of g₂) of g₃) ⇒ (⟦ ⋆ ⟧ A ⇒ (T of ⋆) of ⋆)
fun-to-⋆ g₁ A T g₂ g₃ p = cast (fun (coerceₗ ≾-⋆l p) (coerce-id A) (inject T g₂)) (coerce g₃ ⇒⋆)

ref-to-⋆ : ∀ T g₁ g₂ → (p : BlameLabel) → Cast (Ref (T of g₁) of g₂) ⇒ (Ref (T of ⋆) of ⋆)
ref-to-⋆ T g₁ g₂ p = cast (ref (cast (coerceᵣ-id T) (coerceₗ ≾-⋆l p)) (cast (coerceᵣ-id T) (coerce g₁ ⇒⋆))) (coerce g₂ ⇒⋆)

stamp-ir : ∀ {A B} (c : Cast A ⇒ B) → Irreducible c → ∀ ℓ → Cast A ⇒ stamp B (l ℓ)
stamp-ir (cast cᵣ c̅) (ir-base 𝓋 _) ℓ = cast cᵣ (stampₗ c̅ 𝓋 ℓ)
stamp-ir (cast cᵣ c̅) (ir-ref  𝓋)   ℓ = cast cᵣ (stampₗ c̅ 𝓋 ℓ)
stamp-ir (cast cᵣ c̅) (ir-fun  𝓋)   ℓ = cast cᵣ (stampₗ c̅ 𝓋 ℓ)

stamp-ir-irreducible : ∀ {A B} {c : Cast A ⇒ B} {ℓ}
  → (i : Irreducible c)
  → Irreducible (stamp-ir c i ℓ)
stamp-ir-irreducible {ℓ = ℓ′} (ir-base {ι} {ℓ} {g} 𝓋 x) =
  ir-base (stampₗ-CVal _ 𝓋 _) (stamp-not-id 𝓋 x)
stamp-ir-irreducible (ir-ref 𝓋) = ir-ref (stampₗ-CVal _ 𝓋 _)
stamp-ir-irreducible (ir-fun 𝓋) = ir-fun (stampₗ-CVal _ 𝓋 _)

stamp-ir! : ∀ {A B} (c : Cast A ⇒ B) → Irreducible c → (ℓ : StaticLabel) → Cast A ⇒ stamp B ⋆
stamp-ir! {B = T of g} (cast cᵣ c̅) (ir-base 𝓋 _) ℓ rewrite g⋎̃⋆≡⋆ {g} =
  cast cᵣ (stamp!ₗ c̅ 𝓋 ℓ)
stamp-ir! {B = T of g} (cast cᵣ c̅) (ir-ref  𝓋)   ℓ rewrite g⋎̃⋆≡⋆ {g} =
  cast cᵣ (stamp!ₗ c̅ 𝓋 ℓ)
stamp-ir! {B = T of g} (cast cᵣ c̅) (ir-fun  𝓋)   ℓ rewrite g⋎̃⋆≡⋆ {g} =
  cast cᵣ (stamp!ₗ c̅ 𝓋 ℓ)

stamp-ir!-irreducible : ∀ {A B} {c : Cast A ⇒ B} {ℓ}
  → (i : Irreducible c)
  → Irreducible (stamp-ir! c i ℓ)
stamp-ir!-irreducible {B = T of g} (ir-base 𝓋 x) rewrite g⋎̃⋆≡⋆ {g} =
  ir-base (stamp!ₗ-CVal _ 𝓋 _) λ ()
stamp-ir!-irreducible {B = T of g} (ir-ref 𝓋) rewrite g⋎̃⋆≡⋆ {g} =
  ir-ref (stamp!ₗ-CVal _ 𝓋 _)
stamp-ir!-irreducible {B = T of g} (ir-fun 𝓋) rewrite g⋎̃⋆≡⋆ {g} =
  ir-fun (stamp!ₗ-CVal _ 𝓋 _)


{- Syntactical composition -}
_⨟ᵣ_ : ∀ {T₁ T₂ T₃} → Castᵣ T₁ ⇒ T₂ → Castᵣ T₂ ⇒ T₃ → Castᵣ T₁ ⇒ T₃
_⨟_  : ∀ {A B C} → Cast A ⇒ B → Cast B ⇒ C → Cast A ⇒ C

id .ι       ⨟ᵣ id ι        = id ι
ref c₁ d₁   ⨟ᵣ ref c₂ d₂   = ref  (c₂ ⨟ c₁) (d₁ ⨟ d₂)
fun c̅ c₁ d₁ ⨟ᵣ fun d̅ c₂ d₂ = fun  (d̅ ⊹⊹ c̅) (c₂ ⨟ c₁) (d₁ ⨟ d₂)
cast cᵣ c̅   ⨟  cast dᵣ d̅   = cast (cᵣ ⨟ᵣ dᵣ) (c̅ ⊹⊹ d̅)
