module HeapSecure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import HeapTyping
open import BigStep
open import Erasure

open import BigStepPreservation

{- Related heaps under high PC -}
heap-relate : ∀ {Σ gc A M V μ μ′}
  → [] ; Σ ; gc ; high ⊢ M ⦂ A
  → Σ ⊢ μ
  → l high ≾ gc
  → μ ∣ high ⊢ M ⇓ V ∣ μ′
    ----------------------------------------
  → erase-μ μ ≡ erase-μ μ′
heap-relate ⊢M ⊢μ pc≾gc (⇓-val v) = refl
heap-relate (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-app L⇓ƛN M⇓V N[V]⇓W) =
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢ƛN , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V in
  case canonical-fun ⊢ƛN V-ƛ of λ where
  (Fun-ƛ ⊢N (<:-ty _ (<:-fun gc⋎g<:pc′ A₁<:A _))) →
    case ⟨ pc≾gc , consis-join-<:ₗ-inv gc⋎g<:pc′ ⟩ of λ where
    ⟨ ≾-l h≼h , <:-l h≼h , _ ⟩ →
      let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓ƛN in
      let ϵμ₁≡ϵμ₂ = heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V  in
      let ϵμ₂≡ϵμ′ = heap-relate (substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁)
                                (⊢value-pc (⊢sub ⊢V A₁<:A) (⇓-value M⇓V))) ⊢μ₂ pc≾gc N[V]⇓W in
      trans ϵμ≡ϵμ₁ (trans ϵμ₁≡ϵμ₂ ϵμ₂≡ϵμ′)
heap-relate (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-true L⇓true M⇓V) =
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢true , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true in
  let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓true in
  let ϵμ₁≡ϵμ′ = heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ (consis-join-≾ pc≾gc (low≾ _)) M⇓V in
  trans ϵμ≡ϵμ₁ ϵμ₁≡ϵμ′
heap-relate (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-false L⇓false N⇓V) =
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢false , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false in
  let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓false in
  let ϵμ₁≡ϵμ′ = heap-relate (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ (consis-join-≾ pc≾gc (low≾ _)) N⇓V in
  trans ϵμ≡ϵμ₁ ϵμ₁≡ϵμ′
heap-relate (⊢let ⊢M ⊢N) ⊢μ pc≾gc (⇓-let M⇓V N[V]⇓W) =
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢V , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  let ϵμ≡ϵμ₁  = heap-relate ⊢M ⊢μ pc≾gc M⇓V in
  let ϵμ₁≡ϵμ′ = heap-relate (substitution-pres (relax-Σ ⊢N Σ₁⊇Σ)
                            (⊢value-pc ⊢V (⇓-value M⇓V))) ⊢μ₁ pc≾gc N[V]⇓W in
  trans ϵμ≡ϵμ₁ ϵμ₁≡ϵμ′
heap-relate (⊢ref? ⊢M) ⊢μ pc≾gc (⇓-ref? M⇓V fresh h≼h {- ℓ ≡ high -})
  rewrite heap-relate ⊢M ⊢μ pc≾gc M⇓V =
  refl
heap-relate (⊢ref ⊢M h≼h {- ℓ ≡ high -}) ⊢μ (≾-l h≼h) (⇓-ref M⇓V fresh)
  rewrite heap-relate ⊢M ⊢μ (≾-l h≼h) M⇓V =
  refl
heap-relate (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref M⇓a eq) =
  heap-relate ⊢M ⊢μ pc≾gc M⇓a
heap-relate (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc (⇓-assign? L⇓a M⇓V h≼h)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓a
... | ⟨ Σ₁ , Σ₁⊇Σ  , ⊢a , ⊢μ₁ ⟩
  rewrite heap-relate ⊢L ⊢μ pc≾gc L⇓a
  rewrite heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V =
  refl
heap-relate (⊢assign ⊢L ⊢M h≼h) ⊢μ (≾-l h≼h) (⇓-assign L⇓a M⇓V)
  with ⇓-preserve ⊢L ⊢μ (≾-l h≼h) L⇓a
... | ⟨ Σ₁ , Σ₁⊇Σ  , ⊢a , ⊢μ₁ ⟩
  with canonical-ref ⊢a V-addr
... | Ref-addr _ (<:-ty _ (<:-ref A<:B B<:A))
  with <:-antisym A<:B B<:A
... | refl {- ℓ₁ ≡ high , the reference points to a high cell -}
  rewrite heap-relate ⊢L ⊢μ (≾-l h≼h) L⇓a
  rewrite heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ (≾-l h≼h) M⇓V =
  refl
heap-relate (⊢cast ⊢M) ⊢μ pc≾gc (⇓-cast a M⇓V V⟨c⟩↝N N⇓W) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢V , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  let ϵμ≡ϵμ₁  = heap-relate ⊢M ⊢μ pc≾gc M⇓V in
  let ϵμ₁≡ϵμ′ = heap-relate (applycast-pres (⊢value-pc ⊢V v) v a V⟨c⟩↝N) ⊢μ₁ pc≾gc N⇓W in
  trans ϵμ≡ϵμ₁ ϵμ₁≡ϵμ′
heap-relate (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-cast-true  i L⇓true⟨c⟩  M⇓V V⋎ℓ⟨bc⟩⇓W) =
  let high≾gc⋎g = consis-join-≾ pc≾gc (low≾ _) in
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢true⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true⟨c⟩ in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ high≾gc⋎g M⇓V in
  let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓true⟨c⟩ in
  let ϵμ₁≡ϵμ₂ = heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ high≾gc⋎g M⇓V in
  let ϵμ₂≡ϵμ′ = heap-relate (⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W in
  trans ϵμ≡ϵμ₁ (trans ϵμ₁≡ϵμ₂ ϵμ₂≡ϵμ′)
heap-relate (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-cast-false i L⇓false⟨c⟩ N⇓V V⋎ℓ⟨bc⟩⇓W) =
  let high≾gc⋎g = consis-join-≾ pc≾gc (low≾ _) in
  let v = ⇓-value N⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢false⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false⟨c⟩ in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ high≾gc⋎g N⇓V in
  let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓false⟨c⟩ in
  let ϵμ₁≡ϵμ₂ = heap-relate (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ high≾gc⋎g N⇓V in
  let ϵμ₂≡ϵμ′ = heap-relate (⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W in
  trans ϵμ≡ϵμ₁ (trans ϵμ₁≡ϵμ₂ ϵμ₂≡ϵμ′)
heap-relate (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-fun-cast i L⇓V⟨c⟩ M⇓W elim⇓V′) =
  case ⇓-value L⇓V⟨c⟩ of λ where
  (V-cast v _) →
    let w = ⇓-value M⇓W in
    let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W    , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓W in
    let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
    let ϵμ₁≡ϵμ₂ = heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓W in
    let ϵμ₂≡ϵμ′ = heap-relate (elim-fun-proxy-wt (⊢app (relax-Σ ⊢V⟨c⟩ Σ₂⊇Σ₁) ⊢W) v w i) ⊢μ₂ pc≾gc elim⇓V′ in
    trans ϵμ≡ϵμ₁ (trans ϵμ₁≡ϵμ₂ ϵμ₂≡ϵμ′)
heap-relate (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref-cast   i M⇓V⟨c⟩ !V⟨oc⟩⇓W) =
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V⟨c⟩ in
  case canonical-ref ⊢V⟨c⟩ (⇓-value M⇓V⟨c⟩) of λ where
  (Ref-proxy ref _ _) →
    let ⊢V = ref-wt ref in
    let ϵμ≡ϵμ₁  = heap-relate ⊢M ⊢μ pc≾gc M⇓V⟨c⟩ in
    let ϵμ₁≡ϵμ′ = heap-relate (⊢cast (⊢deref ⊢V)) ⊢μ₁ pc≾gc !V⟨oc⟩⇓W in
    trans ϵμ≡ϵμ₁ ϵμ₁≡ϵμ′
heap-relate (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc (⇓-assign?-cast i L⇓V⟨c⟩ elim⇓W) =
  case ⇓-value L⇓V⟨c⟩ of λ where
  (V-cast v _) →
    let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
    let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
    let ϵμ₁≡ϵμ′ = heap-relate (elim-ref-proxy-wt (⊢assign? ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ)) v i unchecked) ⊢μ₁ pc≾gc elim⇓W in
    trans ϵμ≡ϵμ₁ ϵμ₁≡ϵμ′
heap-relate (⊢assign ⊢L ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-assign-cast  i L⇓V⟨c⟩ elim⇓W) =
  case ⇓-value L⇓V⟨c⟩ of λ where
  (V-cast v _) →
    let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
    let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
    let ϵμ₁≡ϵμ′ = heap-relate (elim-ref-proxy-wt (⊢assign ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ) pc′≼ℓ) v i static) ⊢μ₁ pc≾gc elim⇓W in
    trans ϵμ≡ϵμ₁ ϵμ₁≡ϵμ′
heap-relate (⊢sub ⊢M A<:B) ⊢μ pc≾gc M⇓V = heap-relate ⊢M ⊢μ pc≾gc M⇓V
heap-relate (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M⇓V = heap-relate ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M⇓V
