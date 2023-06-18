open import Common.Types

module CC2.Syntax where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import Common.BlameLabels
open import Common.Coercions public
open import LabelExpr.LabelExpr
  renaming (blame to bl; Irreducible to Ir;
            Progress to Progressₑ; progress to progressₑ) public
open import Memory.Addr


data Op : Set where
  op-addr         : (n : RawAddr) → Op
  op-lam          : Op
  op-app          : (A B : Type) → (ℓ : StaticLabel) → Op
  op-app!         : (A B : Type) → (g :       Label) → Op
  op-const        : ∀ {ι} (k : rep ι) → Op
  op-if           : (A : Type) → (ℓ : StaticLabel) → Op
  op-if!          : (A : Type) → (g :       Label) → Op
  op-let          : (A : Type) → Op
  op-ref          : (ℓ : StaticLabel) → Op
  op-ref?         : (ℓ : StaticLabel) → (p : BlameLabel) → Op
  op-deref        : (A : Type) → (g : Label) → Op
  op-assign       : (T : RawType) → (ℓ̂ ℓ : StaticLabel) → Op
  op-assign?      : (T : RawType) → (ĝ g :       Label) → BlameLabel → Op
  op-cast         : ∀ {A B} → Cast A ⇒ B → Op
  op-prot         : ∀ (A : Type)
    → (pc : LExpr) → LVal pc
    → (ℓ : StaticLabel) → Op
  -- op-prot-cast    : ∀ {g₁ g₂} (A : Type) (c̅ : CoercionExp g₁ ⇒ g₂)
  --   → (ℓ : StaticLabel) → Op
  op-blame        : BlameLabel → Op
  {- Terms that only appear in erasure -}
  op-opaque       : Op

sig : Op → List Sig
sig (op-addr n)        = []
sig op-lam             = (ν ■) ∷ []
sig (op-app  A B ℓ)    = ■ ∷ ■ ∷ []
sig (op-app! A B g)    = ■ ∷ ■ ∷ []
sig (op-const k)       = []
sig (op-if  A ℓ)       = ■ ∷ ■ ∷ ■ ∷ []
sig (op-if! A g)       = ■ ∷ ■ ∷ ■ ∷ []
sig (op-let A)         = ■ ∷ (ν ■) ∷ []
sig (op-ref ℓ)         = ■ ∷ []
sig (op-ref? ℓ p)      = ■ ∷ []
sig (op-deref A g)     = ■ ∷ []
sig (op-assign T ℓ̂ ℓ)  = ■ ∷ ■ ∷ []
sig (op-assign? T ĝ g p) = ■ ∷ ■ ∷ []
sig (op-cast c)        = ■ ∷ []
sig (op-prot A pc v ℓ)   = ■ ∷ []
-- sig (op-prot-cast A c̅ ℓ) = ■ ∷ []
sig (op-blame p)       = []
sig op-opaque          = []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infix 8 _⟨_⟩

pattern addr n             = (op-addr n) ⦅ nil ⦆
pattern ƛ N                = (op-lam) ⦅ cons (bind (ast N)) nil ⦆
pattern app L M A B ℓ      = (op-app A B ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern app! L M A B g     = (op-app! A B g) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_ k               = (op-const k) ⦅ nil ⦆
pattern if L A ℓ M N       = (op-if A ℓ) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern if! L A g M N      = (op-if! A g) ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern `let M A N         = (op-let A) ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern ref⟦_⟧ ℓ M         = (op-ref ℓ) ⦅ cons (ast M) nil ⦆
pattern ref?⟦_⟧ ℓ M p      = (op-ref? ℓ p) ⦅ cons (ast M) nil ⦆
pattern ! M A g            = (op-deref A g) ⦅ cons (ast M) nil ⦆
pattern assign L M T ℓ̂ ℓ   = (op-assign T ℓ̂ ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern assign? L M T ĝ g p = (op-assign? T ĝ g p) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⟨_⟩ M c           = (op-cast c) ⦅ cons (ast M) nil ⦆
pattern prot pc 𝓋 ℓ M A    = (op-prot A pc 𝓋 ℓ) ⦅ cons (ast M) nil ⦆
-- pattern prot-cast c̅ ℓ M A  = (op-prot-cast A c̅ ℓ) ⦅ cons (ast M) nil ⦆
pattern blame p            = (op-blame p) ⦅ nil ⦆
pattern ●                 = op-opaque ⦅ nil ⦆                     {- opaque value -}
