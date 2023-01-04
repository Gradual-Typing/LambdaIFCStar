module CCExpSub.CanonicalForms where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import Common.TypeBasedCast
open import Memory.HeapContext
open import CCExpSub.Syntax Cast_⇒_
open import CCExpSub.Typing Cast_⇒_
open import CCExpSub.Values

open import CCExpSub.Uniqueness


data Fun : Term → HeapContext → Type → Set where
  Fun-ƛ : ∀ {Σ A B N ℓᶜ ℓ}
    → (∀ {pc} → A ∷ [] ; Σ ; l ℓᶜ ; pc ⊢ N ⦂ B)
      ----------------------------------------------------- Lambda
    → Fun (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ) Σ (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ)

  Fun-ƛ↟ : ∀ {Σ A B C N ℓᶜ ℓ} {A→B<:C : ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ <: C}
    → (∀ {pc} → A ∷ [] ; Σ ; l ℓᶜ ; pc ⊢ N ⦂ B)
    → ⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ ≢ C
      ----------------------------------------------------- Lambda Subtyping
    → Fun (ƛ⟦ ℓᶜ ⟧ A ˙ N of ℓ ↟ A→B<:C) Σ C

  Fun-proxy : ∀ {Σ gc₁ gc₂ A₁ A₂ B₁ B₂ g₁ g₂ V}
                {c : Cast (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) ⇒ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)}
    → Fun V Σ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁)
    → Inert c
      ----------------------------------------------------- Function Proxy
    → Fun (V ⟨ c ⟩) Σ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)

  Fun-proxy↟ : ∀ {Σ gc₁ gc₂ A₁ A₂ B₁ B₂ C g₁ g₂ V}
                  {c : Cast (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) ⇒ (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)}
                  {A₂→B₂<:C : ⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂ <: C}
    → Fun V Σ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁)
    → Inert c
    → ⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂ ≢ C
      ----------------------------------------------------- Function Proxy Subtyping
    → Fun ((V ⟨ c ⟩) ↟ A₂→B₂<:C) Σ C

-- Sanity check
fun-is-value : ∀ {Σ V gc A B g}
  → Fun V Σ (⟦ gc ⟧ A ⇒ B of g)
  → Value V
fun-is-value (Fun-ƛ       _)         = V-ƛ
fun-is-value (Fun-ƛ↟     _ neq)     = V-ƛ↟ neq
fun-is-value (Fun-proxy   fun i)     = V-cast (fun-is-value fun) i
fun-is-value (Fun-proxy↟ fun i neq) = V-cast↟ (fun-is-value fun) i neq

-- Canonical form of value of function type
canonical-fun : ∀ {Σ gc pc A B g gᶜ V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ⟦ gᶜ ⟧ A ⇒ B of g
  → Value V
    -------------------------------
  → Fun V Σ (⟦ gᶜ ⟧ A ⇒ B of g)
canonical-fun (⊢lam ⊢N) V-ƛ = Fun-ƛ ⊢N
canonical-fun (⊢cast ⊢V) (V-cast v (I-fun c i₁ i₂)) =
  Fun-proxy (canonical-fun ⊢V v) (I-fun c i₁ i₂)
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-ƛ↟ neq) =
  case canonical-fun ⊢V V-ƛ of λ where
  (Fun-ƛ ⊢N) → Fun-ƛ↟ ⊢N neq
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-cast↟ v i neq) =
  case i of λ where
  (I-fun _ i₁ i₂) → Fun-proxy↟ (canonical-fun (cast-wt-inv ⊢V) v) i neq
canonical-fun {gc = gc} (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-const↟ neq) =
  case uniqueness ⊢V (⊢const {gc = gc}) of λ where ()
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) (V-addr↟ neq) =
  case canonical-fun ⊢V V-addr of λ ()
canonical-fun (⊢sub-pc ⊢V gc<:gc′) v = canonical-fun ⊢V v

data Reference : Term → HeapContext → Type → Set where
  Ref-addr : ∀ {Σ n T ℓ ℓ̂}
    → lookup-Σ Σ (a⟦ ℓ̂ ⟧ n) ≡ just T
      ---------------------------------------------------------- Reference
    → Reference (addr a⟦ ℓ̂ ⟧ n of ℓ) Σ (Ref (T of l ℓ̂) of l ℓ)

  Ref-addr↟ : ∀ {Σ A n T ℓ̂ ℓ} {Ref<:A : Ref (T of l ℓ̂) of l ℓ <: A}
    → lookup-Σ Σ (a⟦ ℓ̂ ⟧ n) ≡ just T
    → Ref (T of l ℓ̂) of l ℓ ≢ A
      ---------------------------------------------------------- Reference Subtyping
    → Reference (addr a⟦ ℓ̂ ⟧ n of ℓ ↟ Ref<:A) Σ A

  Ref-proxy : ∀ {Σ A₁ A₂ g₁ g₂ V} {c : Cast (Ref A₁ of g₁) ⇒ (Ref A₂ of g₂)}
    → Reference V Σ (Ref A₁ of g₁)
    → Inert c
      ------------------------------------------ Reference Proxy
    → Reference (V ⟨ c ⟩) Σ (Ref A₂ of g₂)

  Ref-proxy↟ : ∀ {Σ A₁ A₂ B g₁ g₂ V}
                {c : Cast (Ref A₁ of g₁) ⇒ (Ref A₂ of g₂)}
                {Ref<:B : Ref A₂ of g₂ <: B}
    → Reference V Σ (Ref A₁ of g₁)
    → Inert c
    → Ref A₂ of g₂ ≢ B
      ------------------------------------------ Reference Proxy Subtyping
    → Reference ((V ⟨ c ⟩) ↟ Ref<:B) Σ B

ref-is-value : ∀ {Σ V A g}
  → Reference V Σ (Ref A of g)
  → Value V
ref-is-value (Ref-addr _)            = V-addr
ref-is-value (Ref-proxy ref i)       = V-cast (ref-is-value ref) i
ref-is-value (Ref-addr↟ _ neq)      = V-addr↟ neq
ref-is-value (Ref-proxy↟ ref i neq) = V-cast↟ (ref-is-value ref) i neq

canonical-ref : ∀ {Σ gc pc A g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
  → Value V
    -----------------------------------
  → Reference V Σ (Ref A of g)
canonical-ref (⊢addr eq) V-addr = Ref-addr eq
canonical-ref (⊢cast ⊢V) (V-cast v (I-ref c i₁ i₂)) =
  Ref-proxy (canonical-ref ⊢V v) (I-ref c i₁ i₂)
canonical-ref (⊢sub ⊢V (<:-ty _ (<:-ref _ _))) (V-addr↟ neq) =
  case canonical-ref ⊢V V-addr of λ where
  (Ref-addr eq) → Ref-addr↟ eq neq
canonical-ref (⊢sub ⊢V (<:-ty _ (<:-ref _ _))) (V-cast↟ v i neq) =
  case i of λ where
  (I-ref _ i₁ i₂) → Ref-proxy↟ (canonical-ref (cast-wt-inv ⊢V) v) i neq
canonical-ref {gc = gc} (⊢sub ⊢V (<:-ty _ (<:-ref _ _))) (V-const↟ _) =
  case uniqueness ⊢V (⊢const {gc = gc}) of λ ()
canonical-ref (⊢sub ⊢V (<:-ty _ (<:-ref _ _))) (V-ƛ↟ neq) =
  case canonical-ref ⊢V V-ƛ of λ where ()
canonical-ref (⊢sub-pc ⊢V gc<:gc′) v = canonical-ref ⊢V v

data Constant : Term → Type → Set where
  Const-base : ∀ {ι} {k : rep ι} {ℓ}
      --------------------------------------- Constant
    → Constant ($ k of ℓ) (` ι of l ℓ)

  Const-base↟ : ∀ {A ι} {k : rep ι} {ℓ} {ι<:A : ` ι of l ℓ <: A}
    → ` ι of l ℓ ≢ A
      --------------------------------------- Constant Subtyping
    → Constant ($ k of ℓ ↟ ι<:A) A

  Const-inj : ∀ {M} {ι ℓ} {c : Cast (` ι of l ℓ) ⇒ (` ι of ⋆)}
    → Constant M (` ι of l ℓ)
      ------------------------------------------------------ Constant Injection
    → Constant (M ⟨ c ⟩) (` ι of ⋆)

canonical-const : ∀ {Σ gc pc ι g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ` ι of g
  → Value V
    --------------------------
  → Constant V (` ι of g)
canonical-const ⊢const V-const = Const-base
canonical-const (⊢cast ⊢V) (V-cast v (I-base-inj c)) =
  case canonical-const ⊢V v of λ where
  Const-base          → Const-inj Const-base
  (Const-base↟ neq)  → Const-inj (Const-base↟ neq)
canonical-const (⊢sub ⊢V (<:-ty <:-⋆ <:-ι)) (V-const↟ neq) =
  contradiction refl neq
canonical-const (⊢sub ⊢V (<:-ty (<:-l ℓ₁≼ℓ) <:-ι)) (V-const↟ neq) =
  case canonical-const ⊢V V-const of λ where
  Const-base → Const-base↟ neq
canonical-const (⊢sub ⊢V (<:-ty g₁<:g <:-ι)) (V-cast↟ v (I-base-inj _) neq) =
  case g₁<:g of λ where
  <:-⋆ → contradiction refl neq
canonical-const (⊢sub ⊢V (<:-ty _ <:-ι)) (V-addr↟ _) =
  case canonical-const ⊢V V-addr of λ where ()
canonical-const (⊢sub ⊢V (<:-ty _ <:-ι)) (V-ƛ↟ _) =
  case canonical-const ⊢V V-ƛ of λ where ()
canonical-const (⊢sub-pc ⊢V _) v = canonical-const ⊢V v


data Canonical⋆ : Term → Set where
  -- V ⟨ A ⇒ T of ⋆ ⟩
  inj : ∀ {A T V} {c : Cast A ⇒ T of ⋆}
    → Inert c
      ------------------------------
    → Canonical⋆ (V ⟨ c ⟩)

  -- V ⟨ A ⇒ S of ⋆ ↟ T of ⋆ ⟩
  inj↟ : ∀ {A S T V} {c : Cast A ⇒ S of ⋆} {S<:T : S of ⋆ <: T of ⋆}
    → Inert c
    → S of ⋆ ≢ T of ⋆
      ----------------------------------
    → Canonical⋆ ((V ⟨ c ⟩) ↟ S<:T)

canonical⋆ : ∀ {Σ gc pc V T}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ T of ⋆
  → Value V
    ---------------------------------
  → Canonical⋆ V
canonical⋆ (⊢cast {M = W} ⊢W) (V-cast v i) = inj i
canonical⋆ (⊢sub ⊢W (<:-ty <:-⋆ S<:T)) v =
  case v of λ where
  (V-const↟ neq) →
    case S<:T of λ where
    <:-ι           → case canonical-const ⊢W V-const of λ where ()
    (<:-fun _ _ _) → case canonical-fun   ⊢W V-const of λ where ()
    (<:-ref _ _)   → case canonical-ref   ⊢W V-const of λ where ()
  (V-addr↟  _) →
    case S<:T of λ where
    <:-ι           → case canonical-const ⊢W V-addr of λ where ()
    (<:-fun _ _ _) → case canonical-fun   ⊢W V-addr of λ where ()
    (<:-ref _ _)   → case canonical-ref   ⊢W V-addr of λ where ()
  (V-ƛ↟     _) →
    case S<:T of λ where
    <:-ι           → case canonical-const ⊢W V-ƛ of λ where ()
    (<:-fun _ _ _) → case canonical-fun   ⊢W V-ƛ of λ where ()
    (<:-ref _ _)   → case canonical-ref   ⊢W V-ƛ of λ where ()
  (V-cast↟ _ i neq) → inj↟ i neq
canonical⋆ (⊢sub-pc ⊢V gc<:gc′) v = canonical⋆ ⊢V v

data CanonicalPC⋆ : Term → Set where

  -- V ⟨ C ⇒ ⟦ ⋆ ⟧ A → B of g ⟩
  inj-pc : ∀ {A B C V g} {c : Cast C ⇒ (⟦ ⋆ ⟧ A ⇒ B of g)}
    → Inert c
      -------------------------
    → CanonicalPC⋆ (V ⟨ c ⟩)

  -- V ⟨ C ⇒ ⟦ ⋆ ⟧ A₁ → B₁ of g₁ ↟ ⟦ ⋆ ⟧ A₂ → B₂ of g₂
  inj-pc↟ : ∀ {A₁ A₂ B₁ B₂ C V g₁ g₂}
               {c : Cast C ⇒ (⟦ ⋆ ⟧ A₁ ⇒ B₁ of g₁)}
               {A₁→B₁<:A₂→B₂ : ⟦ ⋆ ⟧ A₁ ⇒ B₁ of g₁ <: ⟦ ⋆ ⟧ A₂ ⇒ B₂ of g₂}
    → Inert c
    → ⟦ ⋆ ⟧ A₁ ⇒ B₁ of g₁ ≢ ⟦ ⋆ ⟧ A₂ ⇒ B₂ of g₂
      --------------------------------------------------
    → CanonicalPC⋆ ((V ⟨ c ⟩) ↟ A₁→B₁<:A₂→B₂)

canonical-pc⋆ : ∀ {Σ gc pc V A B g}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ⟦ ⋆ ⟧ A ⇒ B of g
  → Value V
    ----------------------------
  → CanonicalPC⋆ V
canonical-pc⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) = inj-pc i
canonical-pc⋆ (⊢sub ⊢V (<:-ty g₁<:g₂ (<:-fun <:-⋆ A₂<:A₁ B₁<:B₂))) v =
  case v of λ where
  (V-const↟ _)   → case canonical-fun ⊢V V-const of λ where ()
  (V-addr↟  _)   → case canonical-fun ⊢V V-addr of λ where ()
  (V-ƛ↟     _)   → case canonical-fun ⊢V V-ƛ of λ where ()
  (V-cast↟ _ i neq) → inj-pc↟ i neq
canonical-pc⋆ (⊢sub-pc ⊢V gc<:gc′) v = canonical-pc⋆ ⊢V v

data CanonicalRef⋆ : Term → Set where

  -- V ⟨ A ⇒ Ref (T of ⋆) of g ⟩
  inj-ref : ∀ {A V T g} {c : Cast A ⇒ Ref (T of ⋆) of g}
    → Inert c
      -------------------------
    → CanonicalRef⋆ (V ⟨ c ⟩)

  -- V ⟨ A ⇒ Ref (T₁ of ⋆) of g₁ ↟ Ref (T₂ of ⋆) of g₂
  inj-ref↟ : ∀ {A V T₁ T₂ g₁ g₂}
                {c : Cast A ⇒ Ref (T₁ of ⋆) of g₁}
                {RefT₁<:RefT₂ : Ref (T₁ of ⋆) of g₁ <: Ref (T₂ of ⋆) of g₂}
    → Inert c
    → Ref (T₁ of ⋆) of g₁ ≢ Ref (T₂ of ⋆) of g₂
      --------------------------------------------------
    → CanonicalRef⋆ ((V ⟨ c ⟩) ↟ RefT₁<:RefT₂)

canonical-ref⋆ : ∀ {Σ gc pc V T g}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref (T of ⋆) of g
  → Value V
    ----------------------------
  → CanonicalRef⋆ V
canonical-ref⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) = inj-ref i
canonical-ref⋆ (⊢sub ⊢V (<:-ty g₁<:g₂ (<:-ref (<:-ty <:-⋆ _) _))) v =
  case v of λ where
  (V-const↟ _)   → case canonical-ref ⊢V V-const of λ where ()
  (V-addr↟  _)   → case canonical-ref ⊢V V-addr of λ where ()
  (V-ƛ↟     _)   → case canonical-ref ⊢V V-ƛ of λ where ()
  (V-cast↟ _ i neq) → inj-ref↟ i neq
canonical-ref⋆ (⊢sub-pc ⊢V gc<:gc′) v = canonical-ref⋆ ⊢V v


stamp-inert : ∀ {A B} (c : Cast A ⇒ B)
  → Inert c → ∀ ℓ
  → (Cast (stamp A (l ℓ)) ⇒ (stamp B (l ℓ)))
stamp-inert (cast (` ι of l ℓ₁) (` ι of ⋆) p (~-ty ~⋆ ~-ι))
            (I-base-inj _) ℓ =
  cast (` ι of l (ℓ₁ ⋎ ℓ)) (` ι of ⋆) p (~-ty ~⋆ ~-ι)
stamp-inert (cast (⟦ gc₁ ⟧ A ⇒ B of g₁) (⟦ gc₂ ⟧ C ⇒ D of g₂) p (~-ty g₁~g₂ A→B~C→D))
            (I-fun _ I-label I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) A→B~C→D in
    cast (⟦ gc₁ ⟧ A ⇒ B of (g₁ ⋎̃ l ℓ)) (⟦ gc₂ ⟧ C ⇒ D of (g₂ ⋎̃ l ℓ)) p c~
stamp-inert (cast (Ref A of g₁) (Ref B of g₂) p (~-ty g₁~g₂ RefA~RefB))
            (I-ref _ I-label I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) RefA~RefB in
    cast (Ref A of (g₁ ⋎̃ l ℓ)) (Ref B of (g₂ ⋎̃ l ℓ)) p c~

stamp-inert-inert : ∀ {A B ℓ} {c : Cast A ⇒ B} (i : Inert c) → Inert (stamp-inert c i ℓ)
stamp-inert-inert (I-base-inj c) = I-base-inj _
stamp-inert-inert (I-fun c I-label I-label) = I-fun (stamp-inert c _ _) I-label I-label
stamp-inert-inert (I-ref c I-label I-label) = I-ref (stamp-inert c _ _) I-label I-label

stamp-val : ∀ V → Value V → StaticLabel → Term
stamp-val ($ k of ℓ₁) V-const ℓ = $ k of (ℓ₁ ⋎ ℓ)
stamp-val (addr a of ℓ₁) V-addr ℓ = addr a of (ℓ₁ ⋎ ℓ)
stamp-val (ƛ⟦ pc ⟧ A ˙ N of ℓ₁) V-ƛ ℓ = ƛ⟦ pc ⟧ A ˙ N of (ℓ₁ ⋎ ℓ)
stamp-val (V ⟨ c ⟩) (V-cast v i) ℓ = stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩
stamp-val ● V-● ℓ = ●
{- values with subtyping ↟ -}
stamp-val ($ k of ℓ₁ ↟ A<:B) (V-const↟ {A} {B} A≢B) ℓ =
  case stamp A (l ℓ) ≡? stamp B (l ℓ) of λ where
  (yes _) → $ k of (ℓ₁ ⋎ ℓ)  -- if A ⋎ ℓ = B ⋎ ℓ
  (no  _) → $ k of (ℓ₁ ⋎ ℓ) ↟ stamp-<: A<:B (<:ₗ-refl {l ℓ})
stamp-val (addr a of ℓ₁ ↟ A<:B) (V-addr↟ {A} {B} A≢B) ℓ =
  case stamp A (l ℓ) ≡? stamp B (l ℓ) of λ where
  (yes _) → addr a of (ℓ₁ ⋎ ℓ) -- if A ⋎ ℓ = B ⋎ ℓ
  (no  _) → addr a of (ℓ₁ ⋎ ℓ) ↟ stamp-<: A<:B (<:ₗ-refl {l ℓ})
stamp-val (ƛ⟦ pc ⟧ A ˙ N of ℓ₁ ↟ A₁<:A₂) (V-ƛ↟ {A₁} {A₂} A₁≢A₂) ℓ =
  case stamp A₁ (l ℓ) ≡? stamp A₂ (l ℓ) of λ where
  (yes _) → ƛ⟦ pc ⟧ A ˙ N of (ℓ₁ ⋎ ℓ)
  (no  _) → ƛ⟦ pc ⟧ A ˙ N of (ℓ₁ ⋎ ℓ) ↟ stamp-<: A₁<:A₂ (<:ₗ-refl {l ℓ})
stamp-val ((V ⟨ c ⟩) ↟ B<:C) (V-cast↟ {A} {B} {C} v i B≢C) ℓ =
  case stamp B (l ℓ) ≡? stamp C (l ℓ) of λ where
  (yes _) → stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩
  (no  _) → (stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩) ↟ stamp-<: B<:C (<:ₗ-refl {l ℓ})

-- A stamped value is value
stamp-val-value : ∀ {V ℓ} (v : Value V) → Value (stamp-val V v ℓ)
stamp-val-value V-const = V-const
stamp-val-value V-addr = V-addr
stamp-val-value V-ƛ = V-ƛ
stamp-val-value (V-cast v i) =
  V-cast (stamp-val-value v) (stamp-inert-inert i)
stamp-val-value V-● = V-●
stamp-val-value {V} {ℓ} (V-const↟ {A} {B} _)
  with stamp A (l ℓ) ≡? stamp B (l ℓ)
... | yes _       = V-const
... | no  A⋎ℓ≢B⋎ℓ = V-const↟ A⋎ℓ≢B⋎ℓ
stamp-val-value {V} {ℓ} (V-addr↟ {A} {B} _)
  with stamp A (l ℓ) ≡? stamp B (l ℓ)
... | yes _       = V-addr
... | no  A⋎ℓ≢B⋎ℓ = V-addr↟ A⋎ℓ≢B⋎ℓ
stamp-val-value {V} {ℓ} (V-ƛ↟ {A} {B} _)
  with stamp A (l ℓ) ≡? stamp B (l ℓ)
... | yes _       = V-ƛ
... | no  A⋎ℓ≢B⋎ℓ = V-ƛ↟ A⋎ℓ≢B⋎ℓ
stamp-val-value {V} {ℓ} (V-cast↟ {A} {B} {C} v i _)
  with stamp B (l ℓ) ≡? stamp C (l ℓ)
... | yes _       = V-cast (stamp-val-value v) (stamp-inert-inert i)
... | no  B⋎ℓ≢C⋎ℓ = V-cast↟ (stamp-val-value v) (stamp-inert-inert i) B⋎ℓ≢C⋎ℓ

stamp-val-low : ∀ {V} (v : Value V) → stamp-val V v low ≡ V
stamp-val-low (V-const {ℓ = low})  = refl
stamp-val-low (V-const {ℓ = high}) = refl
stamp-val-low (V-addr {ℓ = low})   = refl
stamp-val-low (V-addr {ℓ = high})  = refl
stamp-val-low (V-ƛ {ℓ = low})      = refl
stamp-val-low (V-ƛ {ℓ = high})     = refl
stamp-val-low (V-cast v (I-base-inj (cast (` ι of l ℓ) (` ι of ⋆) p (~-ty ℓ~⋆ ~-ι))))
  rewrite stamp-val-low v
  with ℓ   | ℓ~⋆
... | low  | ~⋆ = refl
... | high | ~⋆ = refl
stamp-val-low (V-cast v (I-fun (cast (_ of l ℓ₁) (_ of g₂) p (~-ty ℓ₁~g₂ _)) I-label I-label))
  rewrite stamp-val-low v
  with ℓ₁  | g₂     | ℓ₁~g₂
... | high | ⋆      | ~⋆ = refl
... | high | l high | l~ = refl
... | low  | ⋆      | ~⋆ = refl
... | low  | l low  | l~ = refl
stamp-val-low (V-cast v (I-ref (cast (_ of l ℓ₁) (_ of g₂) p (~-ty ℓ₁~g₂ _)) I-label I-label))
  rewrite stamp-val-low v
  with ℓ₁  | g₂     | ℓ₁~g₂
... | high | ⋆      | ~⋆ = refl
... | high | l high | l~ = refl
... | low  | ⋆      | ~⋆ = refl
... | low  | l low  | l~ = refl
stamp-val-low V-● = refl
stamp-val-low (V-const↟ {A} {B} _) with stamp A (l low) ≡? stamp B (l low)
... | yes _ = {!!}
... | no  _ = {!!}

⊢value-pc : ∀ {Γ Σ gc gc′ pc pc′ V A}
  → Γ ; Σ ; gc  ; pc ⊢ V ⦂ A
  → Value V
    ------------------------------------
  → Γ ; Σ ; gc′ ; pc′ ⊢ V ⦂ A
⊢value-pc (⊢addr eq) V-addr = ⊢addr eq
⊢value-pc (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
⊢value-pc ⊢const V-const = ⊢const
⊢value-pc (⊢cast ⊢V) (V-cast v i) = ⊢cast (⊢value-pc ⊢V v)
⊢value-pc (⊢sub ⊢V A<:B) (V-const↟ _)    = ⊢sub (⊢value-pc ⊢V V-const) A<:B
⊢value-pc (⊢sub ⊢V A<:B) (V-addr↟ _)     = ⊢sub (⊢value-pc ⊢V V-addr) A<:B
⊢value-pc (⊢sub ⊢V A<:B) (V-ƛ↟ _)        = ⊢sub (⊢value-pc ⊢V V-ƛ) A<:B
⊢value-pc (⊢sub ⊢V A<:B) (V-cast↟ v i _) = ⊢sub (⊢value-pc ⊢V (V-cast v i)) A<:B
⊢value-pc (⊢sub-pc ⊢V gc<:gc′) v = ⊢value-pc ⊢V v
