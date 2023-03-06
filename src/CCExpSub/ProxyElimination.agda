module CCExpSub.ProxyElimination where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Nat
open import Data.List hiding ([_])
open import Data.Maybe
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Function using (case_of_)

open import Common.Types
open import Common.TypeBasedCast
open import CCExpSub.Statics
open import CCExpSub.CanonicalForms

elim-if : ∀ {V g} → Constant V (` Bool of g) → (A : Type) → (M N : Term) → Term
-- b of ℓ
elim-if (Const (Const-base {k = true} {ℓ}))  A M N = prot ℓ M
elim-if (Const (Const-base {k = false} {ℓ})) A M N = prot ℓ N
-- b of ℓ ⟨ Bool of ℓ ⇒ Bool of ⋆ ⟩
elim-if (Const (Const-inj {c = c} (Const (Const-base {k = true} {ℓ})))) A M N =
  prot ℓ (cast-pc ⋆ M) ⟨ branch/c A c ⟩
elim-if (Const (Const-inj {c = c} (Const (Const-base {k = false} {ℓ})))) A M N =
  prot ℓ (cast-pc ⋆ M) ⟨ branch/c A c ⟩
-- b of ℓ₁ ⟨ Bool of ℓ₁ ↟ Bool of ℓ₂ ⟩ ⟨ Bool of ℓ₂ ⇒ Bool of ⋆ ⟩
elim-if (Const (Const-inj {c = c}
  (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = true} {ℓ₁})))) A M N =
  let s = cast↟ (stamp A (l ℓ₁)) (stamp A (l ℓ₂)) (stamp-<: <:-refl (<:-l ℓ₁≼ℓ₂)) in
  (prot ℓ₁ (cast-pc ⋆ M)) ↟⟨ s ⟩ ⟨ branch/c A c ⟩
elim-if (Const (Const-inj {c = c}
  (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = false} {ℓ₁})))) A M N =
  let s = cast↟ (stamp A (l ℓ₁)) (stamp A (l ℓ₂)) (stamp-<: <:-refl (<:-l ℓ₁≼ℓ₂)) in
  (prot ℓ₁ (cast-pc ⋆ N)) ↟⟨ s ⟩ ⟨ branch/c A c ⟩
-- b of ℓ₁ ⟨ Bool of ℓ₁ ↟ Bool of ℓ₂ ⟩
elim-if (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = true} {ℓ₁})) A M N =
  let s = cast↟ (stamp A (l ℓ₁)) (stamp A (l ℓ₂)) (stamp-<: <:-refl (<:-l ℓ₁≼ℓ₂)) in
  (prot ℓ₁ M) ↟⟨ s ⟩
elim-if (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = false} {ℓ₁})) A M N =
  let s = cast↟ (stamp A (l ℓ₁)) (stamp A (l ℓ₂)) (stamp-<: <:-refl (<:-l ℓ₁≼ℓ₂)) in
  (prot ℓ₁ N) ↟⟨ s ⟩
-- b of ℓ ⟨ Bool of ℓ ⇒ Bool of ⋆ ⟩ ⟨ Bool of ⋆ ↟ Bool of ⋆ ⟩
elim-if (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj {c = c} (Const (Const-base {k = true} {ℓ})))) A M N =
  prot ℓ (cast-pc ⋆ M) ⟨ branch/c A c ⟩
elim-if (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj {c = c} (Const (Const-base {k = false} {ℓ})))) A M N =
  prot ℓ (cast-pc ⋆ N) ⟨ branch/c A c ⟩
-- b of ℓ₁ ⟨ Bool of ℓ₁ ↟ Bool of ℓ₂ ⟩ ⟨ Bool of ℓ₂ ⇒ Bool of ⋆ ⟩ ⟨ Bool of ⋆ ↟ Bool of ⋆ ⟩
elim-if (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj {c = c} (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)}
  (Const-base {k = true} {ℓ₁})))) A M N =
  let s = cast↟ (stamp A (l ℓ₁)) (stamp A (l ℓ₂)) (stamp-<: <:-refl (<:-l ℓ₁≼ℓ₂)) in
  (prot ℓ₁ (cast-pc ⋆ M)) ↟⟨ s ⟩ ⟨ branch/c A c ⟩
elim-if (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj {c = c} (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)}
  (Const-base {k = false} {ℓ₁})))) A M N =
  let s = cast↟ (stamp A (l ℓ₁)) (stamp A (l ℓ₂)) (stamp-<: <:-refl (<:-l ℓ₁≼ℓ₂)) in
  (prot ℓ₁ (cast-pc ⋆ N)) ↟⟨ s ⟩ ⟨ branch/c A c ⟩

elim-if-wt : ∀ {Σ gc pc V M N A g}
  → (b : Constant V (` Bool of g))
  → (∀ {pc} → [] ; Σ ; gc ⋎̃ g ; pc ⊢ M ⦂ A)
  → (∀ {pc} → [] ; Σ ; gc ⋎̃ g ; pc ⊢ N ⦂ A)
    ---------------------------------------------------
  → [] ; Σ ; gc ; pc ⊢ elim-if b A M N ⦂ stamp A g
elim-if-wt (Const (Const-base {k = true} {ℓ})) ⊢M ⊢N = ⊢prot ⊢M
elim-if-wt (Const (Const-base {k = false} {ℓ})) ⊢M ⊢N = ⊢prot ⊢N
elim-if-wt {gc = gc} (Const (Const-inj (Const (Const-base {k = true} {ℓ})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} = ⊢cast (⊢prot (⊢cast-pc ⊢M ~⋆))
elim-if-wt {gc = gc} (Const (Const-inj (Const (Const-base {k = false} {ℓ})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} = ⊢cast (⊢prot (⊢cast-pc ⊢M ~⋆))
elim-if-wt {gc = gc} (Const (Const-inj {c = c}
  (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = true})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} =
  ⊢cast (⊢sub (⊢prot (⊢cast-pc ⊢M ~⋆)))
elim-if-wt {gc = gc} (Const (Const-inj {c = c}
  (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = false})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} =
  ⊢cast (⊢sub (⊢prot (⊢cast-pc ⊢N ~⋆)))
elim-if-wt (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = true} {ℓ₁})) ⊢M ⊢N =
  ⊢sub (⊢prot (⊢sub-pc ⊢M (consis-join-<:ₗ <:ₗ-refl (<:-l ℓ₁≼ℓ₂))))
elim-if-wt (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)} (Const-base {k = false} {ℓ₁})) ⊢M ⊢N =
  ⊢sub (⊢prot (⊢sub-pc ⊢N (consis-join-<:ₗ <:ₗ-refl (<:-l ℓ₁≼ℓ₂))))
elim-if-wt {gc = gc} (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj {c = c} (Const (Const-base {k = true} {ℓ})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} =
  ⊢cast (⊢prot (⊢cast-pc ⊢M ~⋆))
elim-if-wt {gc = gc} (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj {c = c} (Const (Const-base {k = false} {ℓ})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} =
  ⊢cast (⊢prot (⊢cast-pc ⊢N ~⋆))
elim-if-wt {gc = gc} (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)}
  (Const-base {k = true} {ℓ₁})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} =
  ⊢cast (⊢sub (⊢prot (⊢cast-pc ⊢M ~⋆)))
elim-if-wt {gc = gc} (Const-↟ {s = cast↟ (` Bool of ⋆) (` Bool of ⋆) (<:-ty <:-⋆ <:-ι)}
  (Const-inj (Const-↟ {s = cast↟ (` Bool of l ℓ₁) (` Bool of l ℓ₂) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)}
  (Const-base {k = false} {ℓ₁})))) ⊢M ⊢N
  rewrite g⋎̃⋆≡⋆ {gc} =
  ⊢cast (⊢sub (⊢prot (⊢cast-pc ⊢N ~⋆)))

-- elim-fun : ∀ {Σ gc A B V g} → Fun V Σ (⟦ gc ⟧ A ⇒ B of g) → (W : Term) → (pc : StaticLabel) → Term
-- elim-fun (Fun-fun (Fun-ƛ {N = N} {ℓ = ℓ} ⊢N)) W pc = prot ℓ (N [ W ])
-- elim-fun {g = g} (Fun-fun (Fun-proxy {V = V} fun-V (I-fun c I-label I-label))) W pc =
--   case c of λ where
--   (cast (⟦ l pc₁ ⟧ A ⇒ B of l ℓ₁) (⟦ l pc₂ ⟧ C ⇒ D of g₂) p _) →
--     (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
--   (cast (⟦ l pc₁ ⟧ A ⇒ B of l ℓ₁) (⟦ ⋆ ⟧ C ⇒ D of g₂) p _) →
--     case pc ⋎ ℓ₁ ≼? pc₁ of λ where
--     (yes _) → cast-pc (l pc) (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
--     (no  _) → error (stamp B g) (blame p)
-- -- (V ⟨ ⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁ ↟ ⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂ ⟩) · W
-- elim-fun (Fun-↟ {V = V} {cast↟ (⟦ gc₁ ⟧ A₁ ⇒ B₁ of g₁) (⟦ gc₂ ⟧ A₂ ⇒ B₂ of g₂)
--   (<:-ty g₁<:g₂ (<:-fun gc₂<:gc₁ A₂<:A₁ B₁<:B₂))} fun-V) W pc =
--   {!!}
