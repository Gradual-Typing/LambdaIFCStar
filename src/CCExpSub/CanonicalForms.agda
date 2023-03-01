module CCExpSub.CanonicalForms where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Common.SubtypeCast
open import Common.TypeBasedCast
open import Memory.HeapContext
open import CCExpSub.Syntax Cast_⇒_
open import CCExpSub.Typing Cast_⇒_
open import CCExpSub.Values

open import CCExpSub.Uniqueness


data SimpFun : Term → HeapContext → Type → Set
data Fun : Term → HeapContext → Type → Set

data SimpFun where

  Fun-ƛ : ∀ {Σ A B N ℓᶜ ℓ}
    → (∀ {pc} → A ∷ [] ; Σ ; l ℓᶜ ; pc ⊢ N ⦂ B)
      ----------------------------------------------------- Lambda
    → SimpFun (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ) Σ (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ)

  Fun-proxy : ∀ {Σ gc₁ gc₂ A₁ A₂ B₁ B₂ g₁ g₂ V}
                {c : Cast (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) ⇒ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)}
    → Fun V Σ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁)
    → Inert c
      ----------------------------------------------------- Function Proxy
    → SimpFun (V ⟨ c ⟩) Σ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)

data Fun where

  Fun-fun : ∀ {Σ A V} → SimpFun V Σ A → Fun V Σ A

  Fun-↟ : ∀ {Σ A B V} {s : A ↟ B} → SimpFun V Σ A → Fun (V ↟⟨ s ⟩) Σ B

-- Sanity check
fun-is-value : ∀ {Σ V gc A B g}
  → Fun V Σ (⟦ gc ⟧ A ⇒ B of g)
  → Value V
fun-is-value (Fun-fun (Fun-ƛ     _))         = V V-ƛ
fun-is-value (Fun-fun (Fun-proxy fun i))     = V (V-cast (fun-is-value fun) i)
fun-is-value (Fun-↟  (Fun-ƛ _))             = V-↟  V-ƛ
fun-is-value (Fun-↟  (Fun-proxy fun i))     = V-↟  (V-cast (fun-is-value fun) i)

-- Canonical form of value of function type
canonical-fun : ∀ {Σ gc pc A B g gᶜ V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ⟦ gᶜ ⟧ A ⇒ B of g
  → Value V
    -------------------------------
  → Fun V Σ (⟦ gᶜ ⟧ A ⇒ B of g)
canonical-fun (⊢lam ⊢N) (V V-ƛ) = Fun-fun (Fun-ƛ ⊢N)
canonical-fun (⊢cast ⊢V) (V (V-cast v (I-fun c i₁ i₂))) =
  Fun-fun (Fun-proxy (canonical-fun ⊢V v) (I-fun c i₁ i₂))
canonical-fun (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ V-ƛ) =
  case canonical-fun ⊢V (V V-ƛ) of λ where
  (Fun-fun (Fun-ƛ ⊢N)) → Fun-↟ (Fun-ƛ ⊢N)
canonical-fun (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ (V-cast v i)) =
  case canonical-fun ⊢V (V (V-cast v i)) of λ where
  (Fun-fun (Fun-proxy fun i)) → Fun-↟ (Fun-proxy fun i)
canonical-fun {gc = gc} {pc} (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ V-const) =
  case uniqueness ⊢V (⊢const {gc = gc} {pc}) of λ where ()
canonical-fun (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-fun _ _ _))} ⊢V) (V-↟ V-addr) =
  case canonical-fun ⊢V (V V-addr) of λ where
  (Fun-fun ())
canonical-fun (⊢sub-pc ⊢V gc<:gc′) v = canonical-fun ⊢V v

data SimpReference : Term → HeapContext → Type → Set
data Reference : Term → HeapContext → Type → Set

data SimpReference where

  Ref-addr : ∀ {Σ n T ℓ ℓ̂}
    → lookup-Σ Σ (a⟦ ℓ̂ ⟧ n) ≡ just T
      ---------------------------------------------------------- Reference
    → SimpReference (addr a⟦ ℓ̂ ⟧ n of ℓ) Σ (Ref (T of l ℓ̂) of l ℓ)

  Ref-proxy : ∀ {Σ A₁ A₂ g₁ g₂ V} {c : Cast (Ref A₁ of g₁) ⇒ (Ref A₂ of g₂)}
    → Reference V Σ (Ref A₁ of g₁)
    → Inert c
      ------------------------------------------ Reference Proxy
    → SimpReference (V ⟨ c ⟩) Σ (Ref A₂ of g₂)

data Reference where

  Ref-ref : ∀ {Σ A V} → SimpReference V Σ A → Reference V Σ A

  Ref-↟ : ∀ {Σ A B V} {s : A ↟ B} → SimpReference V Σ A → Reference (V ↟⟨ s ⟩) Σ B

ref-is-value : ∀ {Σ V A g}
  → Reference V Σ (Ref A of g)
  → Value V
ref-is-value (Ref-ref (Ref-addr _))       = V V-addr
ref-is-value (Ref-ref (Ref-proxy ref i))  = V (V-cast (ref-is-value ref) i)
ref-is-value (Ref-↟ (Ref-addr _))        = V-↟  V-addr
ref-is-value (Ref-↟ (Ref-proxy ref i))   = V-↟  (V-cast (ref-is-value ref) i)

canonical-ref : ∀ {Σ gc pc A g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
  → Value V
    -----------------------------------
  → Reference V Σ (Ref A of g)
canonical-ref (⊢addr eq) (V V-addr) = Ref-ref (Ref-addr eq)
canonical-ref (⊢cast ⊢V) (V (V-cast v (I-ref c i₁ i₂))) =
  Ref-ref (Ref-proxy (canonical-ref ⊢V v) (I-ref c i₁ i₂))
canonical-ref (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-ref _ _))} ⊢V) (V-↟ V-addr) =
  case canonical-ref ⊢V (V V-addr) of λ where
  (Ref-ref (Ref-addr eq)) → Ref-↟ (Ref-addr eq)
canonical-ref (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-ref _ _))} ⊢V) (V-↟ (V-cast v i)) =
  case canonical-ref ⊢V (V (V-cast v i)) of λ where
  (Ref-ref (Ref-proxy ref i)) → Ref-↟ (Ref-proxy ref i)
canonical-ref {gc = gc} {pc} (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-ref _ _))} ⊢V) (V-↟ V-const) =
  case uniqueness ⊢V (⊢const {gc = gc} {pc}) of λ ()
canonical-ref (⊢sub {s = cast↟ _ _ (<:-ty _ (<:-ref _ _))} ⊢V) (V-↟ V-ƛ) =
  case canonical-ref ⊢V (V V-ƛ) of λ where
  (Ref-ref ())
canonical-ref (⊢sub-pc ⊢V gc<:gc′) v = canonical-ref ⊢V v

data SimpConstant : Term → Type → Set
data Constant : Term → Type → Set

data SimpConstant where

  Const-base : ∀ {ι} {k : rep ι} {ℓ}
      --------------------------------------- Constant
    → SimpConstant ($ k of ℓ) (` ι of l ℓ)

  Const-inj : ∀ {M} {ι ℓ} {c : Cast (` ι of l ℓ) ⇒ (` ι of ⋆)}
    → Constant M (` ι of l ℓ)
      ------------------------------------------------------ Injected Constant
    → SimpConstant (M ⟨ c ⟩) (` ι of ⋆)

data Constant where

  Const : ∀ {A V} → SimpConstant V A → Constant V A

  Const-↟ : ∀ {A B V} {s : A ↟ B} → SimpConstant V A → Constant (V ↟⟨ s ⟩) B

canonical-const : ∀ {Σ gc pc ι g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ` ι of g
  → Value V
    --------------------------
  → Constant V (` ι of g)
canonical-const ⊢const (V V-const) = Const Const-base
canonical-const (⊢cast ⊢V) (V (V-cast v (I-base-inj c))) =
  Const (Const-inj (canonical-const ⊢V v))
canonical-const (⊢sub {s = cast↟ _ _ (<:-ty <:-⋆ <:-ι)} ⊢V) (V-↟ V-const) =
  case canonical-const ⊢V (V V-const) of λ where
  (Const ())
canonical-const (⊢sub {s = cast↟ _ _ (<:-ty (<:-l ℓ₁≼ℓ) <:-ι)} ⊢V) (V-↟ V-const) =
  case canonical-const ⊢V (V V-const) of λ where
  (Const Const-base) → Const-↟ Const-base
canonical-const (⊢sub {s = cast↟ _ _ (<:-ty g₁<:g <:-ι)} ⊢V) (V-↟ (V-cast v i)) =
  case canonical-const ⊢V (V (V-cast v i)) of λ where
  (Const (Const-inj const)) → Const-↟ (Const-inj const)
canonical-const (⊢sub {s = cast↟ _ _ (<:-ty _ <:-ι)} ⊢V) (V-↟ V-addr) =
  case canonical-const ⊢V (V V-addr) of λ where
  (Const ())
canonical-const (⊢sub {s = cast↟ _ _ (<:-ty _ <:-ι)} ⊢V) (V-↟ V-ƛ) =
  case canonical-const ⊢V (V V-ƛ) of λ where
  (Const ())
canonical-const (⊢sub-pc ⊢V _) v = canonical-const ⊢V v
