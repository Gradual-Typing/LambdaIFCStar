module Types where

open import Data.Maybe
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Addr
open import Utils

open import SecurityLabels public


{- **** Types **** -}
data Base : Set where
  Bool : Base
  Unit : Base

rep : Base → Set
rep Bool = 𝔹
rep Unit = ⊤

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


{- **** Type label stamping **** -}
stamp : Type → Label → Type
stamp (T of g₁) g₂ = T of g₁ ⋎̃ g₂

stamp-~ : ∀ {A B g₁ g₂}
  → A ~ B → g₁ ~ₗ g₂
  → stamp A g₁ ~ stamp B g₂
stamp-~ {S of g₁′} {T of g₂′} (~-ty g₁′~g₂′ S~T) g₁~g₂ = ~-ty (consis-join-~ₗ g₁′~g₂′ g₁~g₂) S~T

stamp-<: : ∀ {A B g₁ g₂}
  → A <: B → g₁ <:ₗ g₂
  → stamp A g₁ <: stamp B g₂
stamp-<: (<:-ty g₁′<:g₂′ S<:T) g₁<:g₂ = <:-ty (consis-join-<:ₗ g₁′<:g₂′ g₁<:g₂) S<:T

stamp-low : ∀ A → stamp A (l low) ≡ A
stamp-low (T of ⋆)      = refl
stamp-low (T of l low)  = refl
stamp-low (T of l high) = refl


{- **** Typing contexts **** -}
Context = List Type


infix 5 _⊑_

{- **** Precision **** -}
data _⊑_ : Type → Type → Set where
  ⊑-ι : ∀ {ι g₁ g₂}
    → g₁ ⊑ₗ g₂
      -----------------------------
    → ` ι of g₁ ⊑ ` ι of g₂

  ⊑-ref : ∀ {A B g₁ g₂}
    → A ⊑ B
    → g₁ ⊑ₗ g₂
      ----------------------------------------------
    → Ref A of g₁ ⊑ Ref B of g₂

  ⊑-fun : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → gc₁ ⊑ₗ gc₂
    → A ⊑ B → C ⊑ D
    → g₁ ⊑ₗ g₂
      ----------------------------------------------
    → ⟦ gc₁ ⟧ A ⇒ B of g₁ ⊑ ⟦ gc₂ ⟧ C ⇒ D of g₂
