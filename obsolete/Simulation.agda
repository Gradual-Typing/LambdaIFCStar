module Simulation where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; subst; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import Heap
open import CC
open import ErasedReduction
open import HeapTyping
open import WellTyped

open import Erasure
open import RelatedHeaps


sim : ∀ {Σ gc pc A M₁ M₂ μ₁ μ₁′ μ₂}
  → [] ; Σ ; gc ; pc ⊢ M₁ ⦂ A
  → Σ ⊢ μ₁
  → l pc ≾ gc
  → M₁ ∣ μ₁ ∣ Σ ∣ pc —→ M₂ ∣ μ₂
  → μ₁ ≈ μ₁′
    -----------------------------------------------------------------------
  → ∃[ μ₂′ ] (erase M₁ ∣ μ₁′ ∣ pc —↠ₑ erase M₂ ∣ μ₂′) × (μ₂ ≈ μ₂′)
sim {M₁ = M₁} {M₂} {μ₁} {μ₁′} ⊢M₁ ⊢μ₁ pc≾gc (ξ {F = F} M₁→M₂) μ₁≈ =
  let ⟨ gc′ , B , pc≾gc′ , ⊢M , _ ⟩    = plug-inversion ⊢M₁ pc≾gc in
  let ⟨ μ₂′ , eraseM₁↠eraseM₂ , μ₂≈ ⟩ = sim ⊢M ⊢μ₁ pc≾gc′ M₁→M₂ μ₁≈ in
  ⟨ μ₂′ , erase-plug F eraseM₁↠eraseM₂ , μ₂≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (ξ-err {F}) μ≈ = ⟨ μ₁′ , erase-plug-error F , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (prot-val {V} {ℓ = ℓ} v) μ≈ with ℓ
... | high rewrite erase-stamp-high v =
  ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ discard-val (erase-val-value v) ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | low  =
  ⟨ μ₁′ , eq ∣ μ₁′ ∣ _ ≡∎ , μ≈ ⟩
  where
  eq : erase V ≡ erase (stamp-val V v low)
  eq = cong erase (sym (stamp-val-low v))
sim {gc = gc} {pc} {μ₁ = μ₁} {μ₁′} {μ₂} (⊢prot ⊢M) ⊢μ₁ pc≾gc (prot-ctx {ℓ = ℓ} M₁→M₂) μ₁≈ with ℓ
... | low  rewrite ℓ⋎low≡ℓ {pc} = {- This case is like ξ because pc ⋎ low = pc -}
  sim {μ₁ = μ₁} {μ₁′} ⊢M ⊢μ₁ pc≾gc⋎low M₁→M₂ μ₁≈
  where
  pc≾gc⋎low : l pc ≾ (gc ⋎̃ l low)
  pc≾gc⋎low rewrite g⋎̃low≡g {gc} = pc≾gc
... | high =
  let ⟨ μ₂′ , eraseM₁↠eraseM₂ , μ₂≈μ₂′ ⟩ = sim ⊢M ⊢μ₁ (consis-join-≾ pc≾gc ≾-refl) M₁→M₂ μ₁≈ in
  let eraseM₁↠eraseM₂ = subst (_ ∣ μ₁′ ∣_—↠ₑ _ ∣ μ₂′) (ℓ⋎high≡high {pc}) eraseM₁↠eraseM₂ in
  ⟨ μ₂′ , discard-mult eraseM₁↠eraseM₂ , μ₂≈μ₂′ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (prot-err {ℓ = ℓ}) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ discard-err ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (β {V} {N} {ℓ = ℓ} v) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ β (erase-val-value v) ⟩ eq ∣ _ ∣ _ ≡∎ , μ≈ ⟩
  where
  eq : erase N [ erase V ] ≡ erase (N [ V ])
  eq = {!!}
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ app-● (erase-val-value v) ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (β-if-true {ℓ = ℓ}) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ β-if-true ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ if-true-●     ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (β-if-false {ℓ = ℓ}) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ β-if-false ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ if-false-●      ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim _ ⊢μ₁ _ (β-let x) μ≈ = {!!}
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ ref-static μ≈ =
  ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ ref-static ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (ref?-ok    pc≼ℓ) μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ ref?-ok ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (ref?-fail ¬pc≼ℓ) μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ ref?-fail ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁ = μ₁} {μ₁′} _ ⊢μ₁ _ (ref {V} {a = a} {ℓ} v fresh) μ≈ =
  ⟨ ⟨ a , erase V , ℓ ⟩ ∷ μ₁′ , _ ∣ _ ∣ _ —→⟨ ref (erase-val-value v) ⟩ _ ∣ _ ∣ _ ∎ , μ₂≈μ₂′ ℓ ⟩
  where
  μ₂≈μ₂′ : ∀ ℓ → ⟨ a , V , ℓ ⟩ ∷ μ₁ ≈ ⟨ a , erase V , ℓ ⟩ ∷ μ₁′
  μ₂≈μ₂′ low  = μ≈-low  μ≈
  μ₂≈μ₂′ high = μ≈-high μ≈
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (deref {a = a} {ℓ} {ℓ₁} eq) μ≈ with ℓ
... | high rewrite ℓ⋎high≡high {ℓ₁} = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ deref-● ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | low  with ℓ₁
...   | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ deref-low (μ≈ a eq) ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
...   | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ deref-high ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ assign-static μ≈ =
  ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ assign-static ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (assign?-ok {a = a} {ℓ} {ℓ₁} eq pc≼ℓ₁) μ₁≈ with ℓ
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ assign?-ok● ⟩ _ ∣ _ ∣ _ ∎ , μ₁≈ ⟩
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ assign?-ok  ⟩ _ ∣ _ ∣ _ ∎ , μ₁≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (assign?-fail {a = a} {ℓ} {ℓ₁} eq pc⋠ℓ₁) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ assign?-fail  ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ assign?-fail● ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁ = μ₁} {μ₁′} (⊢assign✓ {ℓ = ℓ′} ⊢a ⊢V pc≼ℓ′) ⊢μ₁ _ (assign {V} {a = a} {ℓ} {ℓ₁} v eq) μ₁≈
  with ℓ₁ | ℓ
... | low  | low  =
  ⟨ ⟨ a , erase V , low ⟩ ∷ μ₁′ ,
     _ ∣ _ ∣ _ —→⟨ assign (erase-val-value v) ⟩ _ ∣ _ ∣ _ ∎ , μ≈-low μ₁≈ ⟩
... | low  | high =  {- This case is impossible -}
 case canonical-ref ⊢a V-addr of λ where
 (Ref-addr eq₁ (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
   case <:-antisym A′<:A A<:A′ of λ where
   refl →
    let ⟨ _ , _ , eq′ , _ ⟩ = ⊢μ₁ _ eq₁ in
    case trans (sym eq) eq′ of λ where
    refl → contradiction ℓ≼ℓ′ λ ()  {- high ⋠ low -}
... | high | low  =
  let ⟨ V′ , eq′ ⟩ = μ₁≈ a eq in
  ⟨ ⟨ a , erase V , high ⟩ ∷ μ₁′  , _ ∣ _ ∣ _ —→⟨ assign (erase-val-value v) ⟩ _ ∣ _ ∣ _ ∎ ,
    μ≈-high μ₁≈ ⟩
... | high | high =
  ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ assign-● (erase-val-value v) ⟩ _ ∣ _ ∣ _ ∎ ,
    μ≈-high-update μ₁≈ eq ⟩
sim {μ₁′ = μ₁′} (⊢cast ⊢V) ⊢μ₁ pc≾gc (cast ⊢V† v a) μ≈ = ⟨ μ₁′ , {!!} , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (if-cast-true {ℓ = ℓ} i) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ β-if-true ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ if-true-●     ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (if-cast-false {ℓ = ℓ} i) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ β-if-false ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ _ —→⟨ if-false-●      ⟩ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim _ ⊢μ₁ _ (fun-cast x x₁ i) = {!!}
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (deref-cast v i) μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim _ ⊢μ₁ _ (assign?-cast x i) = {!!}
sim _ ⊢μ₁ _ (assign-cast x x₁ i) = {!!}
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (β-cast-pc v) μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim (⊢sub ⊢M A<:B)       ⊢μ₁ pc≾gc M₁→M₂ μ≈ = sim ⊢M ⊢μ₁ pc≾gc M₁→M₂ μ≈
sim (⊢sub-pc ⊢M gc<:gc′) ⊢μ₁ pc≾gc M₁→M₂ μ≈ = sim ⊢M ⊢μ₁ (≾-<: pc≾gc gc<:gc′) M₁→M₂ μ≈
