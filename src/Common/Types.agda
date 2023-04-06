module Common.Types where

open import Data.Maybe
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_⇔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Common.Utils
open import Common.SecurityLabels public


{- **** Types **** -}
data Base : Set where
  Bool : Base
  Unit : Base

rep : Base → Set
rep Bool = 𝔹
rep Unit = ⊤

const-eq? : ∀ {ι} → (k₁ k₂ : rep ι) → Dec (k₁ ≡ k₂)
const-eq? {Bool} false false  = yes refl
const-eq? {Bool} false true   = no  λ ()
const-eq? {Bool} true false   = no  λ ()
const-eq? {Bool} true true    = yes refl
const-eq? {Unit} tt tt        = yes refl


data RawType : Set
data Type : Set

infix 10 `_
infix 8  ⟦_⟧_⇒_
infix 7  _of_

data RawType where
  `_      : Base → RawType
  Ref_    : Type → RawType
  ⟦_⟧_⇒_ : Label → Type → Type → RawType

data Type where
  _of_ : RawType → Label → Type

-- -- Well-formed types
-- infix 4 ⊢_

-- data ⊢_ : Type → Set where

--   ⊢ι    : ∀ ι g
--       -----------------
--     → ⊢ ` ι of g

--   ⊢ref  : ∀ {T} {ĝ} {g}
--     → ⊢ T of ĝ
--     → g ≾ ĝ
--       -----------------------------
--     → ⊢ Ref (T of ĝ) of g

--   ⊢fun  : ∀ {A} {B} {gᶜ} {g}
--     → ⊢ A
--     → ⊢ B
--     → g ≾ gᶜ
--       -----------------------------
--     → ⊢ ⟦ gᶜ ⟧ A ⇒ B of g

-- ⊢? : ∀ A → Dec (⊢ A)
-- ⊢? (` ι of g) = yes (⊢ι ι g)
-- ⊢? (Ref (T of ĝ) of g) =
--   case ⊢? (T of ĝ) of λ where
--   (yes ⊢Tg) →
--     case g ≾? ĝ of λ where
--     (yes g≾ĝ) → yes (⊢ref ⊢Tg g≾ĝ)
--     (no  g⋨ĝ) → no λ { (⊢ref _ g≾ĝ) → contradiction g≾ĝ g⋨ĝ }
--   (no ¬⊢Tg) → no λ { (⊢ref ⊢Tg _) → contradiction ⊢Tg ¬⊢Tg }
-- ⊢? (⟦ gᶜ ⟧ A ⇒ B of g) =
--   case ⊢? A of λ where
--   (yes ⊢A) →
--     case ⊢? B of λ where
--     (yes ⊢B) →
--       case g ≾? gᶜ of λ where
--       (yes g≾gᶜ) → yes (⊢fun ⊢A ⊢B g≾gᶜ)
--       (no  g⋨gᶜ) → no λ { (⊢fun _ _ g≾gᶜ) → contradiction g≾gᶜ g⋨gᶜ }
--     (no ¬⊢B) → no λ { (⊢fun _ ⊢B _) → contradiction ⊢B ¬⊢B }
--   (no ¬⊢A) → no λ { (⊢fun ⊢A _ _) → contradiction ⊢A ¬⊢A }

infix 4 _≡ᵣ?_
infix 4 _≡?_

_≡ᵣ?_ : (S T : RawType) → Dec (S ≡ T)
_≡?_ : (A B : Type) → Dec (A ≡ B)

(` Bool) ≡ᵣ? (` Bool) = yes refl
(` Unit) ≡ᵣ? (` Unit) = yes refl
(` Bool) ≡ᵣ? (` Unit) = no λ ()
(` Unit) ≡ᵣ? (` Bool) = no λ ()
(` _) ≡ᵣ? (Ref _) = no λ ()
(` _) ≡ᵣ? (⟦ _ ⟧ _ ⇒ _) = no λ ()
(Ref A) ≡ᵣ? (Ref B) with A ≡? B
... | yes refl = yes refl
... | no  neq = no (λ { refl → contradiction refl neq })
(Ref _) ≡ᵣ? (` _) = no λ ()
(Ref _) ≡ᵣ? (⟦ _ ⟧ x₂ ⇒ _) = no λ ()
(⟦ gc₁ ⟧ A ⇒ B) ≡ᵣ? (⟦ gc₂ ⟧ C ⇒ D)
  with gc₁ ==? gc₂
... | no  neq = no (λ { refl → contradiction refl neq })
... | yes refl with A ≡? C
... | no  neq = no (λ { refl → contradiction refl neq })
... | yes refl with B ≡? D
... | no neq  = no (λ { refl → contradiction refl neq })
... | yes refl = yes refl
(⟦ _ ⟧ _ ⇒ _) ≡ᵣ? (` _) = no λ ()
(⟦ _ ⟧ _ ⇒ _) ≡ᵣ? (Ref _) = no λ ()

(S of g₁) ≡? (T of g₂) with S ≡ᵣ? T
... | no  neq = no (λ { refl → contradiction refl neq })
... | yes refl with g₁ ==? g₂
... | no  neq = no (λ { refl → contradiction refl neq })
... | yes refl = yes refl


{- **** Subtyping **** -}
infix 5 _<:ᵣ_
infix 5 _<:_

data _<:ᵣ_ : RawType → RawType → Set
data _<:_ :  Type → Type → Set

data _<:ᵣ_ where
  <:-ι : ∀ {ι} → ` ι <:ᵣ ` ι

  <:-ref : ∀ {A B}
    → A <: B
    → B <: A
      ----------------
    → Ref A <:ᵣ Ref B

  <:-fun : ∀ {gc₁ gc₂} {A B C D}
    → gc₂ <:ₗ gc₁
    → C <: A
    → B <: D
      ----------------------------------
    → ⟦ gc₁ ⟧ A ⇒ B <:ᵣ ⟦ gc₂ ⟧ C ⇒ D

data _<:_ where
  <:-ty : ∀ {g₁ g₂} {S T}
    → g₁ <:ₗ g₂
    → S  <:ᵣ T
      ---------------------
    → S of g₁ <: T of g₂

<:ᵣ-refl : ∀ {T} → T <:ᵣ T
<:-refl  : ∀ {A} → A <: A

<:ᵣ-refl {` ι}           = <:-ι
<:ᵣ-refl {Ref A}         = <:-ref <:-refl <:-refl
<:ᵣ-refl {⟦ gc ⟧ A ⇒ B} = <:-fun <:ₗ-refl <:-refl <:-refl
<:-refl  {T of g}        = <:-ty <:ₗ-refl <:ᵣ-refl

<:ᵣ-trans : ∀ {S T U} → S <:ᵣ T → T <:ᵣ U → S <:ᵣ U
<:-trans  : ∀ {A B C} → A <: B  → B <: C  → A <: C

<:ᵣ-trans <:-ι <:-ι = <:-ι
<:ᵣ-trans (<:-ref A<:B B<:A) (<:-ref B<:C C<:B) =
  <:-ref (<:-trans A<:B B<:C) (<:-trans C<:B B<:A)
<:ᵣ-trans (<:-fun gc₂<:gc₁ B₁<:A₁ A₂<:B₂) (<:-fun gc₃<:gc₂ C₁<:B₁ B₂<:C₂) =
  <:-fun (<:ₗ-trans gc₃<:gc₂ gc₂<:gc₁) (<:-trans C₁<:B₁ B₁<:A₁) (<:-trans A₂<:B₂ B₂<:C₂)
<:-trans (<:-ty g₁<:g₂ S<:T) (<:-ty g₂<:g₃ T<:U) =
  <:-ty (<:ₗ-trans g₁<:g₂ g₂<:g₃) (<:ᵣ-trans S<:T T<:U)

<:ᵣ-antisym : ∀ {S T} → S <:ᵣ T → T <:ᵣ S → S ≡ T
<:-antisym  : ∀ {A B} → A <:  B → B <:  A → A ≡ B

<:ᵣ-antisym <:-ι <:-ι = refl
<:ᵣ-antisym (<:-ref A<:B B<:A) (<:-ref _ _) = cong Ref_ (<:-antisym A<:B B<:A)
<:ᵣ-antisym {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} (<:-fun gc₂<:gc₁ C<:A B<:D) (<:-fun gc₁<:gc₂ A<:C D<:B) =
  let eq1 : ⟦ gc₁ ⟧ A ⇒ B ≡ ⟦ gc₁ ⟧ C ⇒ D
      eq1 = cong₂ (λ □₁ □₂ → ⟦ gc₁ ⟧ □₁ ⇒ □₂) (<:-antisym A<:C C<:A) (<:-antisym B<:D D<:B)
      eq2 : ⟦ gc₁ ⟧ C ⇒ D ≡ ⟦ gc₂ ⟧ C ⇒ D
      eq2 = cong (λ □ → ⟦ □ ⟧ C ⇒ D) (<:ₗ-antisym gc₁<:gc₂ gc₂<:gc₁) in
    trans eq1 eq2
<:-antisym {S of g₁} {T of g₂} (<:-ty g₁<:g₂ S<:T) (<:-ty g₂<:g₁ T<:S) =
  cong₂ (λ □₁ □₂ → □₁ of □₂) (<:ᵣ-antisym S<:T T<:S) (<:ₗ-antisym g₁<:g₂ g₂<:g₁)


{- **** Consistency **** -}
infix 5 _~ᵣ_
infix 5 _~_

data _~ᵣ_ : RawType → RawType → Set
data _~_  : Type → Type → Set

data _~ᵣ_ where
  ~-ι : ∀ {ι} → ` ι ~ᵣ ` ι

  ~-ref : ∀ {A B}
    → A ~ B
      ---------------
    → Ref A ~ᵣ Ref B

  ~-fun : ∀ {gc₁ gc₂} {A B C D}
    → gc₁ ~ₗ gc₂
    → A ~ C
    → B ~ D
      ---------------------------------
    → ⟦ gc₁ ⟧ A ⇒ B ~ᵣ ⟦ gc₂ ⟧ C ⇒ D

data _~_ where
  ~-ty : ∀ {g₁ g₂} {S T}
    → g₁ ~ₗ g₂
    → S  ~ᵣ T
      --------------------
    → S of g₁ ~ T of g₂

~ᵣ-refl : ∀ {T} → T ~ᵣ T
~-refl : ∀ {A} → A ~ A

~ᵣ-refl {` ι}           = ~-ι
~ᵣ-refl {Ref A}         = ~-ref ~-refl
~ᵣ-refl {⟦ gc ⟧ A ⇒ B} = ~-fun ~ₗ-refl ~-refl ~-refl
~-refl  {T of g}        = ~-ty ~ₗ-refl ~ᵣ-refl

~ᵣ-sym : ∀ {S T} → S ~ᵣ T → T ~ᵣ S
~-sym  : ∀ {A B} → A ~ B → B ~ A

~ᵣ-sym ~-ι = ~-ι
~ᵣ-sym (~-ref A~B) = ~-ref (~-sym A~B)
~ᵣ-sym (~-fun gc₁~gc₂ A~C B~D) = ~-fun (~ₗ-sym gc₁~gc₂) (~-sym A~C) (~-sym B~D)
~-sym  (~-ty g₁~g₂ S~T) = ~-ty (~ₗ-sym g₁~g₂) (~ᵣ-sym S~T)


{- **** Consistent subtyping **** -}
infix 5 _≲ᵣ_     -- of raw types
infix 5 _≲_      -- of types

data _≲ᵣ_ : RawType → RawType → Set
data _≲_  : Type → Type → Set

data _≲ᵣ_ where
  ≲-ι : ∀ {ι} → ` ι ≲ᵣ ` ι

  ≲-ref : ∀ {A B}
    → A ≲ B
    → B ≲ A
      -----------------
    → Ref A ≲ᵣ Ref B

  ≲-fun : ∀ {gc₁ gc₂} {A B C D}
    → gc₂ ≾ gc₁
    → C ≲ A
    → B ≲ D
      -----------------------------------
    → ⟦ gc₁ ⟧ A ⇒ B ≲ᵣ ⟦ gc₂ ⟧ C ⇒ D

data _≲_ where
  ≲-ty : ∀ {g₁ g₂} {S T}
    → g₁ ≾ g₂
    → S ≲ᵣ T
      --------------------
    → S of g₁ ≲ T of g₂

≲ᵣ-refl : ∀ {T} → T ≲ᵣ T
≲-refl  : ∀ {A} → A ≲ A

≲ᵣ-refl {` ι}           = ≲-ι
≲ᵣ-refl {Ref A}         = ≲-ref ≲-refl ≲-refl
≲ᵣ-refl {⟦ gc ⟧ A ⇒ B} = ≲-fun ≾-refl ≲-refl ≲-refl
≲-refl  {T of g}        = ≲-ty ≾-refl ≲ᵣ-refl

≲ᵣ-antisym : ∀ {S T}
  → S ≲ᵣ T → T ≲ᵣ S
  → S ~ᵣ T
≲-antisym : ∀ {A B}
  → A ≲ B → B ≲ A
  → A ~ B

≲ᵣ-antisym ≲-ι ≲-ι = ~-ι
≲ᵣ-antisym (≲-ref A≲B B≲A) (≲-ref _ _) =
  ~-ref (≲-antisym A≲B B≲A)
≲ᵣ-antisym (≲-fun gc₂≾gc₁ C≲A B≲D) (≲-fun gc₁≾gc₂ A≲C D≲B) =
  ~-fun (≾-antisym gc₁≾gc₂ gc₂≾gc₁) (≲-antisym A≲C C≲A) (≲-antisym B≲D D≲B)
≲-antisym (≲-ty g₁≾g₂ S≲T) (≲-ty g₂≾g₁ T≲S) =
  ~-ty (≾-antisym g₁≾g₂ g₂≾g₁) (≲ᵣ-antisym S≲T T≲S)

A≲Tg→A≲T⋆ : ∀ {A T g} → A ≲ T of g → A ≲ T of ⋆
A≲Tg→A≲T⋆ {T₁ of g₁} {T₂} {g₂} (≲-ty g₁≾g₂ T₁≲T₂) =
  ≲-ty ≾-⋆r T₁≲T₂

{- Properties of consistent subtyping (≲):
        B
   ≲  / | <:
     /  |
    A - C
      ~
        B
   ≲  / | ~
     /  |
    A - C
      <:
-}
≲ᵣ-prop : ∀ {S T : RawType}
  → S ≲ᵣ T
  → ∃[ U ] (S ~ᵣ U) × (U <:ᵣ T)
≲-prop : ∀ {A B : Type}
  → A ≲ B
  → ∃[ C ] (A ~ C) × (C <: B)

≲ᵣ-prop′ : ∀ {S T : RawType}
  → S ≲ᵣ T
  → ∃[ U ] (S <:ᵣ U) × (U ~ᵣ T)
≲-prop′ : ∀ {A B : Type}
  → A ≲ B
  → ∃[ C ] (A <: C) × (C ~ B)

≲ᵣ-prop′ {` ι} {` ι} ≲-ι = ⟨ ` ι , <:-ι , ~-ι ⟩
≲ᵣ-prop′ {Ref A} {Ref B} (≲-ref A≲B B≲A) =
  ⟨ Ref A , <:ᵣ-refl , ~-ref (≲-antisym A≲B B≲A) ⟩
≲ᵣ-prop′ {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} (≲-fun gc₂≾gc₁ C≲A B≲D) =
  case ≾-prop gc₂≾gc₁ of λ where
    ⟨ gc , gc₂~gc , gc<:gc₁ ⟩ →
      case ⟨ ≲-prop C≲A , ≲-prop′ B≲D ⟩ of λ where
        ⟨ ⟨ A′ , C~A′ , A′<:A ⟩ , ⟨ B′ , B<:B′ , B′~D ⟩ ⟩ →
          ⟨ ⟦ gc ⟧ A′ ⇒ B′ , <:-fun gc<:gc₁ A′<:A B<:B′ , ~-fun (~ₗ-sym gc₂~gc) (~-sym C~A′) B′~D ⟩

≲-prop′ {S of g₁} {T of g₂} (≲-ty g₁≾g₂ S≲T) =
  case ≾-prop′ g₁≾g₂ of λ where
    ⟨ g , g₁<:g , g~g₂ ⟩ →
      case ≲ᵣ-prop′ S≲T of λ where
        ⟨ U , S<:U , U~T ⟩ →
          ⟨ U of g , <:-ty g₁<:g S<:U , ~-ty g~g₂ U~T ⟩

≲ᵣ-prop {` ι} {` ι} ≲-ι = ⟨ ` ι , ~-ι , <:-ι ⟩
≲ᵣ-prop {Ref A} {Ref B} (≲-ref A≲B B≲A) =
  ⟨ Ref B , ~-ref (≲-antisym A≲B B≲A) , <:ᵣ-refl ⟩
≲ᵣ-prop {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} (≲-fun gc₂≾gc₁ C≲A B≲D) =
  case ≾-prop′ gc₂≾gc₁ of λ where
    ⟨ gc , gc₂<:gc , gc~gc₁ ⟩ →
      case ⟨ ≲-prop′ C≲A , ≲-prop B≲D ⟩ of λ where
        ⟨ ⟨ A′ , C<:A′ , A′~A ⟩ , ⟨ B′ , B~B′ , B′<:D ⟩ ⟩ →
          ⟨ ⟦ gc ⟧ A′ ⇒ B′ ,
            ~-fun (~ₗ-sym gc~gc₁) (~-sym A′~A) B~B′ , <:-fun gc₂<:gc C<:A′ B′<:D ⟩

≲-prop {S of g₁} {T of g₂} (≲-ty g₁≾g₂ S≲T) =
  case ≾-prop g₁≾g₂ of λ where
    ⟨ g , g₁~g , g<:g₂ ⟩ →
      case ≲ᵣ-prop S≲T of λ where
        ⟨ U , S~U , U<:T ⟩ →
          ⟨ U of g , ~-ty g₁~g S~U , <:-ty g<:g₂ U<:T ⟩

-- Consistency implies consistent subtyping (both directions)
~ᵣ→≲ᵣ : ∀ {S T} → S ~ᵣ T → S ≲ᵣ T × T ≲ᵣ S
~→≲ : ∀ {A B} → A ~ B → A ≲ B × B ≲ A

~ᵣ→≲ᵣ ~-ι = ⟨ ≲-ι , ≲-ι ⟩
~ᵣ→≲ᵣ (~-ref A~B) =
  case ~→≲ A~B of λ where
    ⟨ A≲B , B≲A ⟩ → ⟨ ≲-ref A≲B B≲A , ≲-ref B≲A A≲B ⟩
~ᵣ→≲ᵣ (~-fun gc₁~gc₂ A~C B~D) =
  case ~ₗ→≾ gc₁~gc₂ of λ where
    ⟨ gc₁≾gc₂ , gc₂≾gc₁ ⟩ →
      case ⟨ ~→≲ A~C , ~→≲ B~D ⟩ of λ where
        ⟨ ⟨ A≲C , C≲A ⟩ , ⟨ B≲D , D≲B ⟩ ⟩ →
          ⟨ ≲-fun gc₂≾gc₁ C≲A B≲D , ≲-fun gc₁≾gc₂ A≲C D≲B ⟩
~→≲ (~-ty g₁~g₂ S~T) =
  case ⟨ ~ₗ→≾ g₁~g₂ , ~ᵣ→≲ᵣ S~T ⟩ of λ where
    ⟨ ⟨ g₁≾g₂ , g₂≾g₁ ⟩ , ⟨ S≲T , T≲S ⟩ ⟩ →
      ⟨ ≲-ty g₁≾g₂ S≲T , ≲-ty g₂≾g₁ T≲S ⟩


{- **** Gradual meet **** -}
infix 5 _⊓ᵣ_
infix 5 _⊓_

_⊓ᵣ_ : RawType → RawType → Maybe RawType
_⊓_ : Type → Type → Maybe Type

` Unit ⊓ᵣ ` Unit = just (` Unit)
` Bool ⊓ᵣ ` Bool = just (` Bool)
Ref A ⊓ᵣ Ref B =
  do
    A⊓B ← A ⊓ B
    just (Ref A⊓B)
⟦ gc₁ ⟧ A ⇒ B ⊓ᵣ ⟦ gc₂ ⟧ C ⇒ D =
  do
    gc₁⊓gc₂ ← gc₁ ⊓ₗ gc₂
    A⊓C ← A ⊓ C
    B⊓D ← B ⊓ D
    just (⟦ gc₁⊓gc₂ ⟧ A⊓C ⇒ B⊓D)
_ ⊓ᵣ _ = nothing

S of g₁ ⊓ T of g₂ =
  do
    S⊓T   ← S ⊓ᵣ T
    g₁⊓g₂ ← g₁ ⊓ₗ g₂
    just (S⊓T of g₁⊓g₂)

grad-meet-~ᵣ : ∀ {S T U} → S ⊓ᵣ T ≡ just U → S ~ᵣ U × T ~ᵣ U
grad-meet-~  : ∀ {A B C} → A ⊓  B ≡ just C → A ~  C × B ~  C

grad-meet-~ᵣ {` Bool} {` Bool} {` Bool} refl = ⟨ ~-ι , ~-ι ⟩
grad-meet-~ᵣ {` Unit} {` Unit} {` Unit} refl = ⟨ ~-ι , ~-ι ⟩
grad-meet-~ᵣ {Ref A} {Ref B} {U}
  with A ⊓ B in A⊓B≡C
... | just C =
  case grad-meet-~ {A} {B} A⊓B≡C of λ where
    ⟨ A~C , B~C ⟩ →
      λ { refl → ⟨ ~-ref A~C , ~-ref B~C ⟩ }
grad-meet-~ᵣ {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} {U}
  with gc₁ ⊓ₗ gc₂ in gc₁⊓gc₂≡gc | A ⊓ C in A⊓C≡A′ | B ⊓ D in B⊓D≡B′
... | just gc | just A′ | just B′ =
  case grad-meet-~ₗ gc₁⊓gc₂≡gc of λ where
    ⟨ gc₁~gc , gc₂~gc ⟩ →
      case ⟨ grad-meet-~ {A} {C} A⊓C≡A′ , grad-meet-~ {B} {D} B⊓D≡B′ ⟩ of λ where
        ⟨ ⟨ A~A′ , C~A′ ⟩ , ⟨ B~B′ , D~B′ ⟩ ⟩ →
          λ { refl → ⟨ ~-fun gc₁~gc A~A′ B~B′ , ~-fun gc₂~gc C~A′ D~B′ ⟩ }
grad-meet-~ {S of g₁} {T of g₂} {C}
  with S ⊓ᵣ T in S⊓T≡U | g₁ ⊓ₗ g₂ in g₁⊓g₂≡g
... | just U | just g =
  case ⟨ grad-meet-~ᵣ {S} {T} S⊓T≡U , grad-meet-~ₗ g₁⊓g₂≡g ⟩ of λ where
    ⟨ ⟨ S~U , T~U ⟩ , ⟨ g₁~g , g₂~g ⟩ ⟩ →
      λ { refl → ⟨ ~-ty g₁~g S~U , ~-ty g₂~g T~U ⟩ }


{- **** Consistent join **** -}
infix 5 _∨̃ᵣ_
infix 5 _∨̃_
{- **** Consistent meet **** -}
infix 5 _∧̃ᵣ_
infix 5 _∧̃_

_∨̃ᵣ_ : RawType → RawType → Maybe RawType
_∧̃ᵣ_ : RawType → RawType → Maybe RawType
_∨̃_ :  Type    → Type    → Maybe Type
_∧̃_ :  Type    → Type    → Maybe Type

` Unit ∨̃ᵣ ` Unit = just (` Unit)
` Bool ∨̃ᵣ ` Bool = just (` Bool)
Ref A ∨̃ᵣ Ref B =
  do
  A⊓B ← A ⊓ B
  just (Ref A⊓B)
⟦ gc₁ ⟧ A ⇒ B ∨̃ᵣ ⟦ gc₂ ⟧ C ⇒ D =
  do
    A∧̃C ← A ∧̃ C
    B∨̃D ← B ∨̃ D
    just (⟦ gc₁ ⋏̃ gc₂ ⟧ A∧̃C ⇒ B∨̃D)
_ ∨̃ᵣ _ = nothing

` Unit ∧̃ᵣ ` Unit = just (` Unit)
` Bool ∧̃ᵣ ` Bool = just (` Bool)
Ref A ∧̃ᵣ Ref B =
  do
    A⊓B ← A ⊓ B
    just (Ref A⊓B)
⟦ gc₁ ⟧ A ⇒ B ∧̃ᵣ ⟦ gc₂ ⟧ C ⇒ D =
  do
    A∨̃C ← A ∨̃ C
    B∧̃D ← B ∧̃ D
    just (⟦ gc₁ ⋎̃ gc₂ ⟧ A∨̃C ⇒ B∧̃D)
_ ∧̃ᵣ _ = nothing

S of g₁ ∨̃ T of g₂ =
  do
    S∨̃T ← S ∨̃ᵣ T
    just (S∨̃T of g₁ ⋎̃ g₂)

S of g₁ ∧̃ T of g₂ =
  do
    S∧̃T ← S ∧̃ᵣ T
    just (S∧̃T of g₁ ⋏̃ g₂)


consis-join-≲ᵣ-inv : ∀ {S T U}
  → S ∨̃ᵣ T ≡ just U → S ≲ᵣ U × T ≲ᵣ U
consis-meet-≲ᵣ-inv : ∀ {S T U}
  → S ∧̃ᵣ T ≡ just U → U ≲ᵣ S × U ≲ᵣ T
consis-join-≲-inv : ∀ {A B C}
  → A ∨̃ B ≡ just C → A ≲ C × B ≲ C
consis-meet-≲-inv : ∀ {A B C}
  → A ∧̃ B ≡ just C → C ≲ A × C ≲ B

consis-join-≲ᵣ-inv {` Bool} {` Bool} {` Bool} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-join-≲ᵣ-inv {` Unit} {` Unit} {` Unit} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-join-≲ᵣ-inv {` Bool} {Ref _} {_} ()
consis-join-≲ᵣ-inv {` Unit} {Ref _} {_} ()
consis-join-≲ᵣ-inv {` Bool} {⟦ _ ⟧ _ ⇒ _} {_} ()
consis-join-≲ᵣ-inv {` Unit} {⟦ _ ⟧ _ ⇒ _} {_} ()
consis-join-≲ᵣ-inv {Ref A} {Ref B} {U}
  with A ⊓ B in A⊓B≡C
... | just C =
  case grad-meet-~ {A} {B} A⊓B≡C of λ where
    ⟨ A~C , B~C ⟩ →
      case ⟨ ~→≲ A~C , ~→≲ B~C ⟩ of λ where
        ⟨ ⟨ A≲C , C≲A ⟩ , ⟨ B≲C , C≲B ⟩ ⟩ →
          λ { refl → ⟨ ≲-ref A≲C C≲A , ≲-ref B≲C C≲B ⟩ }
consis-join-≲ᵣ-inv {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} {U}
  with A ∧̃ C in A∧̃C≡A′ | B ∨̃ D in B∨̃D≡B′
... | just A′ | just B′ =
  case consis-meet-≾-inv {gc₁} {gc₂} refl of λ where
    ⟨ gc₁⋏̃gc₂≾gc₁ , gc₁⋏̃gc₂≾gc₂ ⟩ →
      case ⟨ consis-meet-≲-inv {A} {C} A∧̃C≡A′ , consis-join-≲-inv {B} {D} B∨̃D≡B′ ⟩ of λ where
        ⟨ ⟨ A′≲A , A′≲C ⟩ , ⟨ B≲B′ , D≲B′ ⟩ ⟩ →
          λ { refl → ⟨ ≲-fun gc₁⋏̃gc₂≾gc₁ A′≲A B≲B′ , ≲-fun gc₁⋏̃gc₂≾gc₂ A′≲C D≲B′ ⟩ }
consis-join-≲-inv {S of g₁} {T of g₂} {C}
  with S ∨̃ᵣ T in S∨̃T≡U
... | just U =
  case ⟨ consis-join-≲ᵣ-inv {S} {T} S∨̃T≡U , consis-join-≾-inv {g₁} {g₂} refl ⟩ of λ where
    ⟨ ⟨ S≲U , T≲U ⟩ , ⟨ g₁≾g₁⋎̃g₂ , g₂≾g₁⋎̃g₂ ⟩ ⟩ →
      λ { refl → ⟨ ≲-ty g₁≾g₁⋎̃g₂ S≲U , ≲-ty g₂≾g₁⋎̃g₂ T≲U ⟩ }

consis-meet-≲ᵣ-inv {` Bool} {` Bool} {` Bool} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-meet-≲ᵣ-inv {` Unit} {` Unit} {` Unit} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-meet-≲ᵣ-inv {` Bool} {Ref _} {_} ()
consis-meet-≲ᵣ-inv {` Unit} {Ref _} {_} ()
consis-meet-≲ᵣ-inv {` Bool} {⟦ _ ⟧ _ ⇒ _} {_} ()
consis-meet-≲ᵣ-inv {` Unit} {⟦ _ ⟧ _ ⇒ _} {_} ()
consis-meet-≲ᵣ-inv {Ref A} {Ref B} {U}
  with A ⊓ B in A⊓B≡C
... | just C =
  case grad-meet-~ {A} {B} A⊓B≡C of λ where
    ⟨ A~C , B~C ⟩ →
      case ⟨ ~→≲ A~C , ~→≲ B~C ⟩ of λ where
        ⟨ ⟨ A≲C , C≲A ⟩ , ⟨ B≲C , C≲B ⟩ ⟩ →
          λ { refl → ⟨ ≲-ref C≲A A≲C , ≲-ref C≲B B≲C ⟩ }
consis-meet-≲ᵣ-inv {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} {U}
  with A ∨̃ C in A∨̃C≡A′ | B ∧̃ D in B∧̃D≡B′
... | just A′ | just B′ =
  case consis-join-≾-inv {gc₁} {gc₂} refl of λ where
    ⟨ gc₁≾gc₁⋎̃gc₂ , gc₂≾gc₁⋎̃gc₂ ⟩ →
      case ⟨ consis-join-≲-inv {A} {C} A∨̃C≡A′ , consis-meet-≲-inv {B} {D} B∧̃D≡B′ ⟩ of λ where
        ⟨ ⟨ A≲A′ , C≲A′ ⟩ , ⟨ B′≲B , B′≲D ⟩ ⟩ →
          λ { refl → ⟨ ≲-fun gc₁≾gc₁⋎̃gc₂ A≲A′ B′≲B , ≲-fun gc₂≾gc₁⋎̃gc₂ C≲A′ B′≲D ⟩ }
consis-meet-≲-inv {S of g₁} {T of g₂} {C}
  with S ∧̃ᵣ T in S∧̃T≡U
... | just U =
  case ⟨ consis-meet-≲ᵣ-inv {S} {T} S∧̃T≡U , consis-meet-≾-inv {g₁} {g₂} refl ⟩ of λ where
    ⟨ ⟨ U≲S , U≲T ⟩ , ⟨ g₁⋏̃g₂≾g₁ , g₁⋏̃g₂≾g₂ ⟩ ⟩ →
      λ { refl → ⟨ ≲-ty g₁⋏̃g₂≾g₁ U≲S , ≲-ty g₁⋏̃g₂≾g₂ U≲T ⟩ }


{- **** Precision **** -}
infix 5 _⊑ᵣ_
infix 5 _⊑_

data _⊑ᵣ_ : RawType → RawType → Set
data _⊑_  : Type → Type → Set

data _⊑ᵣ_ where
  ⊑-ι : ∀ {ι}
      -----------------------------
    → ` ι ⊑ᵣ ` ι

  ⊑-ref : ∀ {A B}
    → A ⊑ B
      ----------------------------------------------
    → Ref A ⊑ᵣ Ref B

  ⊑-fun : ∀ {A B C D gc₁ gc₂}
    → gc₁ ⊑ₗ gc₂
    → A ⊑ C
    → B ⊑ D
      ----------------------------------------------
    → ⟦ gc₁ ⟧ A ⇒ B ⊑ᵣ ⟦ gc₂ ⟧ C ⇒ D

data _⊑_ where
  ⊑-ty : ∀ {S T g₁ g₂}
    → g₁ ⊑ₗ g₂
    → S  ⊑ᵣ T
      --------------------
    → S of g₁ ⊑ T of g₂

infix 4 _⊑?_

_⊑?_ : (A B : Type) → Dec (A ⊑ B)
(` ι₁ of g₁) ⊑? (` ι₂ of g₂) =
  case (` ι₁) ≡ᵣ? (` ι₂) of λ where
  (yes refl) →
    case g₁ ⊑ₗ? g₂ of λ where
    (yes g₁⊑g₂) → yes (⊑-ty g₁⊑g₂ ⊑-ι)
    (no  g₁⋤g₂)  → no λ { (⊑-ty g₁⊑g₂ ⊑-ι) → contradiction g₁⊑g₂ g₁⋤g₂ }
  (no ι₁≢ι₂) → no λ { (⊑-ty _ ⊑-ι) → contradiction refl ι₁≢ι₂ }
(` ι of g₁) ⊑? (Ref _ of _) = no λ { (⊑-ty _ ()) }
(` ι of g₁) ⊑? (⟦ _ ⟧ _ ⇒ _ of _) = no λ { (⊑-ty _ ()) }
(Ref A of g₁) ⊑? (Ref B of g₂) =
  case A ⊑? B of λ where
  (yes A⊑B) →
    case g₁ ⊑ₗ? g₂ of λ where
    (yes g₁⊑g₂) → yes (⊑-ty g₁⊑g₂ (⊑-ref A⊑B))
    (no  g₁⋤g₂) → no λ { (⊑-ty g₁⊑g₂ (⊑-ref _)) → contradiction g₁⊑g₂ g₁⋤g₂ }
  (no  A⋤B) → no λ { (⊑-ty _ (⊑-ref A⊑B)) → contradiction A⊑B A⋤B }
(Ref A of g₁) ⊑? (` _ of _) = no λ { (⊑-ty _ ()) }
(Ref A of g₁) ⊑? (⟦ _ ⟧ _ ⇒ _ of _) = no λ { (⊑-ty _ ()) }
⟦ gᶜ₁ ⟧ A₁ ⇒ B₁ of g₁ ⊑? ⟦ gᶜ₂ ⟧ A₂ ⇒ B₂ of g₂ =
  case gᶜ₁ ⊑ₗ? gᶜ₂ of λ where
  (yes gᶜ₁⊑gᶜ₂) →
    case A₁ ⊑? A₂ of λ where
    (yes A₁⊑A₂) →
      case B₁ ⊑? B₂ of λ where
      (yes B₁⊑B₂) →
        case g₁ ⊑ₗ? g₂ of λ where
          (yes g₁⊑g₂) → yes (⊑-ty g₁⊑g₂ (⊑-fun gᶜ₁⊑gᶜ₂ A₁⊑A₂ B₁⊑B₂))
          (no  g₁⋤g₂) → no λ { (⊑-ty g₁⊑g₂ (⊑-fun _ _ _)) → contradiction g₁⊑g₂ g₁⋤g₂ }
      (no  B₁⋤B₂) → no λ { (⊑-ty _ (⊑-fun _ _ B₁⊑B₂)) → contradiction B₁⊑B₂ B₁⋤B₂ }
    (no  A₁⋤A₂) → no λ { (⊑-ty _ (⊑-fun _ A₁⊑A₂ _)) → contradiction A₁⊑A₂ A₁⋤A₂ }
  (no  gᶜ₁⋤gᶜ₂) → no λ { (⊑-ty _ (⊑-fun gᶜ₁⊑gᶜ₂ _ _)) → contradiction gᶜ₁⊑gᶜ₂ gᶜ₁⋤gᶜ₂ }
(⟦ _ ⟧ _ ⇒ _ of _) ⊑? (` _ of _) = no λ { (⊑-ty _ ()) }
(⟦ _ ⟧ _ ⇒ _ of _) ⊑? (Ref _ of _) = no λ { (⊑-ty _ ()) }


{- **** Precision-subtyping **** -}
infix 5 _⊑:>ᵣ_
infix 5 _⊑:>_
infix 5 _⊑<:ᵣ_
infix 5 _⊑<:_

data _⊑:>ᵣ_ : RawType → RawType → Set
data _⊑:>_  : Type    → Type    → Set
data _⊑<:ᵣ_ : RawType → RawType → Set
data _⊑<:_  : Type    → Type    → Set

data _⊑:>ᵣ_ where
  ⊑:>-ι : ∀ {ι} → ` ι ⊑:>ᵣ ` ι

  ⊑:>-ref : ∀ {A B}
    -- → A ⊑:> B → A ⊑<: B
    → A ⊑ B
      --------------------
    → Ref A ⊑:>ᵣ Ref B

  ⊑:>-fun : ∀ {A B C D gc₁ gc₂}
    → gc₁ ⊑<:ₗ gc₂
    → A ⊑<: C
    → B ⊑:> D
      ----------------------------------------------
    → ⟦ gc₁ ⟧ A ⇒ B ⊑:>ᵣ ⟦ gc₂ ⟧ C ⇒ D

data _⊑:>_ where
  ⊑:>-ty : ∀ {S T g₁ g₂}
    → g₁ ⊑:>ₗ g₂
    → S  ⊑:>ᵣ T
      --------------------
    → S of g₁ ⊑:> T of g₂

data _⊑<:ᵣ_ where
  ⊑<:-ι : ∀ {ι} → ` ι ⊑<:ᵣ ` ι

  ⊑<:-ref : ∀ {A B}
    -- → A ⊑<: B → A ⊑:> B
    → A ⊑ B
      --------------------
    → Ref A ⊑<:ᵣ Ref B

  ⊑<:-fun : ∀ {A B C D gc₁ gc₂}
    → gc₁ ⊑:>ₗ gc₂
    → A ⊑:> C
    → B ⊑<: D
      ----------------------------------------------
    → ⟦ gc₁ ⟧ A ⇒ B ⊑<:ᵣ ⟦ gc₂ ⟧ C ⇒ D

data _⊑<:_ where
  ⊑<:-ty : ∀ {S T g₁ g₂}
    → g₁ ⊑<:ₗ g₂
    → S  ⊑<:ᵣ T
      --------------------
    → S of g₁ ⊑<: T of g₂

⊑:>ᵣ-prop-from : ∀ {T₁ T₂} → T₁ ⊑:>ᵣ T₂ → ∃[ S ] (T₁ ⊑ᵣ S) × (T₂ <:ᵣ S)
⊑:>-prop-from  : ∀ {A B} → A ⊑:> B → ∃[ C ] (A ⊑ C) × (B <: C)
⊑<:ᵣ-prop-from : ∀ {T₁ T₂} → T₁ ⊑<:ᵣ T₂ → ∃[ S ] (T₁ ⊑ᵣ S) × (S <:ᵣ T₂)
⊑<:-prop-from  : ∀ {A B} → A ⊑<: B → ∃[ C ] (A ⊑ C) × (C <: B)

⊑:>ᵣ-prop-from {` ι} ⊑:>-ι = ⟨ ` ι , ⊑-ι , <:-ι ⟩
⊑:>ᵣ-prop-from {Ref A} {Ref B} (⊑:>-ref A⊑B) =
  ⟨ Ref B , ⊑-ref A⊑B , <:ᵣ-refl ⟩
⊑:>ᵣ-prop-from {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} (⊑:>-fun gc₁⊑<:gc₂ A⊑<:C B⊑:>D) =
  let ⟨ gc , gc₁⊑gc , gc<:gc₂ ⟩ = ⊑<:ₗ-prop-from gc₁⊑<:gc₂
      ⟨ E  , A⊑E , E<:C ⟩ = ⊑<:-prop-from A⊑<:C
      ⟨ F  , B⊑F , D<:F ⟩ = ⊑:>-prop-from B⊑:>D in
  ⟨ ⟦ gc ⟧ E ⇒ F , ⊑-fun gc₁⊑gc A⊑E B⊑F , <:-fun gc<:gc₂ E<:C D<:F ⟩
⊑:>-prop-from {T₁ of g₁} {T₂ of g₂} (⊑:>-ty g₁⊑:>g₂ T₁⊑:>T₂) =
  let ⟨ g , g₁⊑g , g₂<:g ⟩ = ⊑:>ₗ-prop-from g₁⊑:>g₂
      ⟨ S , T₁⊑S , T₂<:S ⟩ = ⊑:>ᵣ-prop-from T₁⊑:>T₂ in
  ⟨ S of g , ⊑-ty g₁⊑g T₁⊑S , <:-ty g₂<:g T₂<:S ⟩

⊑<:ᵣ-prop-from {` ι} ⊑<:-ι = ⟨ ` ι , ⊑-ι , <:-ι ⟩
⊑<:ᵣ-prop-from {Ref A} {Ref B} (⊑<:-ref A⊑B) =
  ⟨ Ref B , ⊑-ref A⊑B , <:ᵣ-refl ⟩
⊑<:ᵣ-prop-from {⟦ gc₁ ⟧ A ⇒ B} {⟦ gc₂ ⟧ C ⇒ D} (⊑<:-fun gc₁⊑:>gc₂ A⊑:>C B⊑<:D) =
  let ⟨ gc , gc₁⊑gc , gc₂<:gc ⟩ = ⊑:>ₗ-prop-from gc₁⊑:>gc₂
      ⟨ E  , A⊑E , C<:E ⟩ = ⊑:>-prop-from A⊑:>C
      ⟨ F  , B⊑F , F<:D ⟩ = ⊑<:-prop-from B⊑<:D in
  ⟨ ⟦ gc ⟧ E ⇒ F , ⊑-fun gc₁⊑gc A⊑E B⊑F , <:-fun gc₂<:gc C<:E F<:D ⟩
⊑<:-prop-from {T₁ of g₁} {T₂ of g₂} (⊑<:-ty g₁⊑<:g₂ T₁⊑<:T₂) =
  let ⟨ g , g₁⊑g , g<:g₂ ⟩ = ⊑<:ₗ-prop-from g₁⊑<:g₂
      ⟨ S , T₁⊑S , S<:T₂ ⟩ = ⊑<:ᵣ-prop-from T₁⊑<:T₂ in
  ⟨ S of g , ⊑-ty g₁⊑g T₁⊑S , <:-ty g<:g₂ S<:T₂ ⟩


⊑:>ᵣ-prop-to : ∀ {T₁ T₂} → ∃[ S ] (T₁ ⊑ᵣ S) × (T₂ <:ᵣ S) → T₁ ⊑:>ᵣ T₂
⊑:>-prop-to  : ∀ {A B} → ∃[ C ] (A ⊑ C) × (B <: C) → A ⊑:> B
⊑<:ᵣ-prop-to : ∀ {T₁ T₂} → ∃[ S ] (T₁ ⊑ᵣ S) × (S <:ᵣ T₂) → T₁ ⊑<:ᵣ T₂
⊑<:-prop-to  : ∀ {A B} → ∃[ C ] (A ⊑ C) × (C <: B) → A ⊑<: B

⊑:>ᵣ-prop-to ⟨ ` ι , ⊑-ι , <:-ι ⟩ = ⊑:>-ι
⊑:>ᵣ-prop-to ⟨ Ref C , ⊑-ref A⊑C , <:-ref B<:C C<:B ⟩
  rewrite <:-antisym B<:C C<:B = ⊑:>-ref A⊑C
⊑:>ᵣ-prop-to ⟨ ⟦ gc ⟧ E ⇒ F , ⊑-fun gc₁⊑gc A⊑E B⊑F , <:-fun gc<:gc₂ E<:C D<:F ⟩ =
  ⊑:>-fun (⊑<:ₗ-prop-to ⟨ gc , gc₁⊑gc , gc<:gc₂ ⟩) (⊑<:-prop-to ⟨ E , A⊑E , E<:C ⟩) (⊑:>-prop-to ⟨ F , B⊑F , D<:F ⟩)
⊑:>-prop-to ⟨ S of g , ⊑-ty g₁⊑g T₁⊑S , <:-ty g₂<:g T₂<:S ⟩ =
  ⊑:>-ty (⊑:>ₗ-prop-to ⟨ g , g₁⊑g , g₂<:g ⟩) (⊑:>ᵣ-prop-to ⟨ S , T₁⊑S , T₂<:S ⟩)

⊑<:ᵣ-prop-to ⟨ ` ι , ⊑-ι , <:-ι ⟩ = ⊑<:-ι
⊑<:ᵣ-prop-to ⟨ Ref C , ⊑-ref A⊑C , <:-ref C<:B B<:C ⟩
  rewrite <:-antisym B<:C C<:B = ⊑<:-ref A⊑C
⊑<:ᵣ-prop-to ⟨ ⟦ gc ⟧ E ⇒ F , ⊑-fun gc₁⊑gc A⊑E B⊑F , <:-fun gc₂<:gc C<:E F<:D ⟩ =
  ⊑<:-fun (⊑:>ₗ-prop-to ⟨ gc , gc₁⊑gc , gc₂<:gc ⟩) (⊑:>-prop-to ⟨ E , A⊑E , C<:E ⟩) (⊑<:-prop-to ⟨ F , B⊑F , F<:D ⟩)
⊑<:-prop-to ⟨ S of g , ⊑-ty g₁⊑g T₁⊑S , <:-ty g<:g₂ S<:T₂ ⟩ =
  ⊑<:-ty (⊑<:ₗ-prop-to ⟨ g , g₁⊑g , g<:g₂ ⟩) (⊑<:ᵣ-prop-to ⟨ S , T₁⊑S , S<:T₂ ⟩)

{- Properties of precision-subtyping -}
⊑:>-prop : _⊑:>_ ⇔ λ A B → ∃[ C ] (A ⊑ C) × (B <: C)
⊑:>-prop = ⟨ ⊑:>-prop-from , ⊑:>-prop-to ⟩

⊑<:-prop : _⊑<:_ ⇔ λ A B → ∃[ C ] (A ⊑ C) × (C <: B)
⊑<:-prop = ⟨ ⊑<:-prop-from , ⊑<:-prop-to ⟩

{- Precision-subtyping is decidable -}
_⊑:>ᵣ?_ : ∀ S T → Dec (S ⊑:>ᵣ T)
_⊑:>?_  : ∀ A B → Dec (A ⊑:>  B)
_⊑<:ᵣ?_ : ∀ S T → Dec (S ⊑<:ᵣ T)
_⊑<:?_  : ∀ A B → Dec (A ⊑<:  B)

(` Unit) ⊑:>ᵣ? (` Unit) = yes ⊑:>-ι
(` Bool) ⊑:>ᵣ? (` Unit) = no λ ()
(` Unit) ⊑:>ᵣ? (` Bool) = no λ ()
(` Bool) ⊑:>ᵣ? (` Bool) = yes ⊑:>-ι
(` _) ⊑:>ᵣ? (Ref _) = no λ ()
(` _) ⊑:>ᵣ? (⟦ _ ⟧ _ ⇒ _) = no λ ()
(Ref _) ⊑:>ᵣ? (` _) = no λ ()
(Ref A) ⊑:>ᵣ? (Ref B) =
  case A ⊑? B of λ where
  (yes A⊑B) → yes (⊑:>-ref A⊑B)
  (no  A⋤B) → no λ { (⊑:>-ref A⊑B) → contradiction A⊑B A⋤B }
(Ref _) ⊑:>ᵣ? (⟦ _ ⟧ _ ⇒ _) = no λ ()
(⟦ _ ⟧ _ ⇒ _) ⊑:>ᵣ? (` _) = no λ ()
(⟦ _ ⟧ _ ⇒ _) ⊑:>ᵣ? (Ref _) = no λ ()
(⟦ gc₁ ⟧ A ⇒ B) ⊑:>ᵣ? (⟦ gc₂ ⟧ C ⇒ D) =
  case gc₁ ⊑<:ₗ? gc₂ of λ where
  (yes gc₁⊑<:gc₂) →
    case A ⊑<:? C of λ where
    (yes A⊑<:C) →
      case B ⊑:>? D of λ where
      (yes B⊑:>D) → yes (⊑:>-fun gc₁⊑<:gc₂ A⊑<:C B⊑:>D)
      (no ¬B⊑:>D) → no λ { (⊑:>-fun _ _ B⊑:>D) → contradiction B⊑:>D ¬B⊑:>D }
    (no ¬A⊑<:C) → no λ { (⊑:>-fun _ A⊑<:C _) → contradiction A⊑<:C ¬A⊑<:C }
  (no ¬gc₁⊑<:gc₂) →
    no λ { (⊑:>-fun gc₁⊑<:gc₂ _ _) → contradiction gc₁⊑<:gc₂ ¬gc₁⊑<:gc₂ }
(S of g₁) ⊑:>? (T of g₂) =
  case S ⊑:>ᵣ? T of λ where
  (yes S⊑:>T) →
    case g₁ ⊑:>ₗ? g₂ of λ where
    (yes g₁⊑:>g₂) → yes (⊑:>-ty g₁⊑:>g₂ S⊑:>T)
    (no ¬g₁⊑:>g₂) → no λ { (⊑:>-ty g₁⊑:>g₂ _) → contradiction g₁⊑:>g₂ ¬g₁⊑:>g₂ }
  (no ¬S⊑:>T) →
    no (λ { (⊑:>-ty _ S⊑:>T) → contradiction S⊑:>T ¬S⊑:>T })

(` Unit) ⊑<:ᵣ? (` Unit) = yes ⊑<:-ι
(` Bool) ⊑<:ᵣ? (` Unit) = no λ ()
(` Unit) ⊑<:ᵣ? (` Bool) = no λ ()
(` Bool) ⊑<:ᵣ? (` Bool) = yes ⊑<:-ι
(` _) ⊑<:ᵣ? (Ref _) = no λ ()
(` _) ⊑<:ᵣ? (⟦ _ ⟧ _ ⇒ _) = no λ ()
(Ref _) ⊑<:ᵣ? (` _) = no λ ()
(Ref A) ⊑<:ᵣ? (Ref B) =
  case A ⊑? B of λ where
  (yes A⊑B) → yes (⊑<:-ref A⊑B)
  (no  A⋤B) → no λ { (⊑<:-ref A⊑B) → contradiction A⊑B A⋤B }
(Ref _) ⊑<:ᵣ? (⟦ _ ⟧ _ ⇒ _) = no λ ()
(⟦ _ ⟧ _ ⇒ _) ⊑<:ᵣ? (` _) = no λ ()
(⟦ _ ⟧ _ ⇒ _) ⊑<:ᵣ? (Ref _) = no λ ()
(⟦ gc₁ ⟧ A ⇒ B) ⊑<:ᵣ? (⟦ gc₂ ⟧ C ⇒ D) =
  case gc₁ ⊑:>ₗ? gc₂ of λ where
  (yes gc₁⊑:>gc₂) →
    case A ⊑:>? C of λ where
    (yes A⊑:>C) →
      case B ⊑<:? D of λ where
      (yes B⊑<:D) → yes (⊑<:-fun gc₁⊑:>gc₂ A⊑:>C B⊑<:D)
      (no ¬B⊑<:D) → no λ { (⊑<:-fun _ _ B⊑<:D) → contradiction B⊑<:D ¬B⊑<:D }
    (no ¬A⊑:>C) → no λ { (⊑<:-fun _ A⊑:>C _) → contradiction A⊑:>C ¬A⊑:>C }
  (no ¬gc₁⊑:>gc₂) →
    no λ { (⊑<:-fun gc₁⊑:>gc₂ _ _) → contradiction gc₁⊑:>gc₂ ¬gc₁⊑:>gc₂ }
(S of g₁) ⊑<:? (T of g₂) =
  case S ⊑<:ᵣ? T of λ where
  (yes S⊑<:T) →
    case g₁ ⊑<:ₗ? g₂ of λ where
    (yes g₁⊑<:g₂) → yes (⊑<:-ty g₁⊑<:g₂ S⊑<:T)
    (no ¬g₁⊑<:g₂) → no λ { (⊑<:-ty g₁⊑<:g₂ _) → contradiction g₁⊑<:g₂ ¬g₁⊑<:g₂ }
  (no ¬S⊑<:T) →
    no (λ { (⊑<:-ty _ S⊑<:T) → contradiction S⊑<:T ¬S⊑<:T })


{- **** Type label stamping **** -}
stamp : Type → Label → Type
stamp (T of g₁) g₂ = T of g₁ ⋎̃ g₂

stamp-low : ∀ A → stamp A (l low) ≡ A
stamp-low (T of ⋆)      = refl
stamp-low (T of l low)  = refl
stamp-low (T of l high) = refl

stamp-~  : ∀ {A B g₁ g₂} → A ~ B → g₁ ~ₗ g₂ → stamp A g₁ ~ stamp B g₂
stamp-~ {S of g₁′} {T of g₂′} (~-ty g₁′~g₂′ S~T) g₁~g₂ = ~-ty (consis-join-~ₗ g₁′~g₂′ g₁~g₂) S~T

stamp-<: : ∀ {A B g₁ g₂} → A <: B → g₁ <:ₗ g₂ → stamp A g₁ <: stamp B g₂
stamp-<: (<:-ty g₁′<:g₂′ S<:T) g₁<:g₂ = <:-ty (consis-join-<:ₗ g₁′<:g₂′ g₁<:g₂) S<:T

stamp-⊑ : ∀ {A B g₁ g₂} → A ⊑ B → g₁ ⊑ₗ g₂ → stamp A g₁ ⊑ stamp B g₂
stamp-⊑ (⊑-ty g₁′⊑g₂′ S⊑T) g₁⊑g₂ = ⊑-ty (consis-join-⊑ₗ g₁′⊑g₂′ g₁⊑g₂) S⊑T


{- **** Typing contexts **** -}
Context = List Type
-- Ctxt    = List (∃[ A ] (⊢ A))
