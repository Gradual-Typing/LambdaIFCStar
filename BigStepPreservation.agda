module BigStepPreservation where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; trans)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import HeapTyping
open import BigStep

open import WellTyped public
open import Preservation public


⇓-preserve : ∀ {Σ gc pc M V A μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → μ ∣ pc ⊢ M ⇓ V ∣ μ′
    ---------------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; pc ⊢ V ⦂ A) × (Σ′ ⊢ μ′)
⇓-preserve {Σ} {μ = μ} ⊢V ⊢μ pc≾gc (⇓-val v) = ⟨ Σ , ⊇-refl Σ , ⊢V , ⊢μ ⟩
⇓-preserve (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-app L⇓ƛN M⇓V N[V]⇓W) =
  let v = ⇓-value M⇓V
      w = ⇓-value N[V]⇓W in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢ƛN , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V in
  case canonical-fun ⊢ƛN V-ƛ of λ where
  (Fun-ƛ ⊢N (<:-ty ℓ<:g (<:-fun gc⋎g<:gc′ A<:A′ B′<:B))) →
    let gc⋎ℓ<:gc⋎g = consis-join-<:ₗ <:ₗ-refl ℓ<:g
        gc⋎ℓ<:gc′  = <:ₗ-trans gc⋎ℓ<:gc⋎g gc⋎g<:gc′
        pc⋎ℓ≾gc′   = ≾-<: (consis-join-≾ pc≾gc ≾-refl) gc⋎ℓ<:gc′ in
    let ⊢N[V] = substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁) (⊢value-pc (⊢sub ⊢V A<:A′) v) in
    let ⟨ Σ₃ , Σ₃⊇Σ₂ , ⊢W , ⊢μ₃ ⟩ = ⇓-preserve ⊢N[V] ⊢μ₂ pc⋎ℓ≾gc′ N[V]⇓W in
    ⟨ Σ₃ , ⊇-trans Σ₃⊇Σ₂ (⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ) ,
      (⊢sub (stamp-val-wt (⊢value-pc ⊢W w) w) (stamp-<: B′<:B ℓ<:g)) , ⊢μ₃ ⟩
⇓-preserve (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-true L⇓true M⇓V) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢true , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true in
  case const-label-≼ ⊢true of λ where
  ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
    let pc⋎ℓ≾gc⋎ℓ′ = consis-join-≾ pc≾gc (≾-l ℓ≼ℓ′) in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎ℓ′ M⇓V in
    let A⋎ℓ<:A⋎ℓ′ = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
    ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ ,
      ⊢sub (stamp-val-wt (⊢value-pc ⊢V v) v) A⋎ℓ<:A⋎ℓ′ , ⊢μ₂ ⟩
⇓-preserve (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-false L⇓false N⇓V) =
  let v = ⇓-value N⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢false , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false in
  case const-label-≼ ⊢false of λ where
  ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
    let pc⋎ℓ≾gc⋎ℓ′ = consis-join-≾ pc≾gc (≾-l ℓ≼ℓ′) in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎ℓ′ N⇓V in
    let A⋎ℓ<:A⋎ℓ′ = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
    ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ ,
      ⊢sub (stamp-val-wt (⊢value-pc ⊢V v) v) A⋎ℓ<:A⋎ℓ′ , ⊢μ₂ ⟩
⇓-preserve (⊢let ⊢M ⊢N) ⊢μ pc≾gc (⇓-let M⇓V N[V]⇓W) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  let ⊢N[V] = substitution-pres (relax-Σ ⊢N Σ₁⊇Σ) (⊢value-pc ⊢V v) in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩ = ⇓-preserve ⊢N[V] ⊢μ₁ pc≾gc N[V]⇓W in
  ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢W , ⊢μ₂ ⟩
⇓-preserve (⊢ref? {T = T} ⊢M) ⊢μ pc≾gc (⇓-ref? {n = n} {ℓ} M⇓V fresh pc≼ℓ) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  ⟨ cons-Σ (a[ ℓ ] n) T Σ₁ , ⊇-trans (⊇-fresh (a[ ℓ ] n) T ⊢μ₁ fresh) Σ₁⊇Σ ,
    ⊢addr (lookup-Σ-cons (a[ ℓ ] n) Σ₁) , ⊢μ-new (⊢value-pc ⊢V v) v ⊢μ₁ fresh ⟩
⇓-preserve (⊢ref {T = T} ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-ref {n = n} {ℓ} M⇓V fresh) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  ⟨ cons-Σ (a[ ℓ ] n) T Σ₁ , ⊇-trans (⊇-fresh (a[ ℓ ] n) T ⊢μ₁ fresh) Σ₁⊇Σ ,
    ⊢addr (lookup-Σ-cons (a[ ℓ ] n) Σ₁) , ⊢μ-new (⊢value-pc ⊢V v) v ⊢μ₁ fresh ⟩
⇓-preserve (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v†} {ℓ = ℓ} {ℓ₁} M⇓a eq) =
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢a , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓a in
  case canonical-ref ⊢a V-addr of λ where
  (Ref-addr {n = n} {g = l ℓ′} eq₁ (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
    case <:-antisym A′<:A A<:A′ of λ where
    refl →
      let ⟨ wf , V , v , eq′ , ⊢V ⟩ = ⊢μ₁ n ℓ₁ eq₁ in
      case trans (sym eq) eq′ of λ where
      refl →
        let leq : ℓ₁ ⋎ (ℓ₁ ⋎ ℓ) ≼ ℓ₁ ⋎ ℓ′
            leq = subst (λ □ → □ ≼ _) (sym ℓ₁⋎[ℓ₁⋎ℓ]≡ℓ₁⋎ℓ) (join-≼′ ≼-refl ℓ≼ℓ′) in
        ⟨ Σ₁ , Σ₁⊇Σ , ⊢sub (stamp-val-wt (⊢value-pc ⊢V v) v†) (<:-ty (<:-l leq) <:ᵣ-refl) , ⊢μ₁ ⟩
⇓-preserve (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc (⇓-assign? {n = n} {ℓ} {ℓ₁} L⇓a M⇓V pc≼ℓ₁) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢a , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓a in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V in
  case canonical-ref ⊢a V-addr of λ where
  (Ref-addr eq (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
    case <:-antisym A′<:A A<:A′ of λ where
    refl →
      let eq′ = Σ₂⊇Σ₁ (a[ ℓ₁ ] n) eq in
      ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢const , ⊢μ-update (⊢value-pc ⊢V v) v ⊢μ₂ eq′ ⟩
⇓-preserve (⊢assign ⊢L ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-assign {n = n} {ℓ} {ℓ₁} L⇓a M⇓V) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢a , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓a in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V in
  case canonical-ref ⊢a V-addr of λ where
  (Ref-addr eq (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
    case <:-antisym A′<:A A<:A′ of λ where
    refl →
      let eq′ = Σ₂⊇Σ₁ (a[ ℓ₁ ] n) eq in
      ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢const , ⊢μ-update (⊢value-pc ⊢V v) v ⊢μ₂ eq′ ⟩
⇓-preserve (⊢cast ⊢M) ⊢μ pc≾gc (⇓-cast a M⇓V V⟨c⟩↝N N⇓W) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩ = ⇓-preserve (applycast-pres (⊢value-pc ⊢V v) v a V⟨c⟩↝N) ⊢μ₁ pc≾gc N⇓W in
  ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢W , ⊢μ₂ ⟩
⇓-preserve {gc = gc} {pc} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-cast-true {ℓ = ℓ} i L⇓true⟨c⟩ M⇓V V⋎ℓ⟨bc⟩⇓W) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢true⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true⟨c⟩ in
  case canonical-const ⊢true⟨c⟩ (⇓-value L⇓true⟨c⟩) of λ where
  (Const-inj _) →  {- g = ⋆ -}
    let pc⋎ℓ≾gc⋎g : l (pc ⋎ ℓ) ≾ (gc ⋎̃ ⋆)
        pc⋎ℓ≾gc⋎g = subst (λ □ → _ ≾ □) (sym (g⋎̃⋆≡⋆ {gc})) ≾-⋆r in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎g M⇓V in
    let ⊢V⋎ℓ⟨bc⟩ = ⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v) in
    let ⟨ Σ₃ , Σ₃⊇Σ₂ , ⊢W , ⊢μ₃ ⟩ = ⇓-preserve ⊢V⋎ℓ⟨bc⟩ ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W in
    ⟨ Σ₃ , ⊇-trans Σ₃⊇Σ₂ (⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ) , ⊢W , ⊢μ₃ ⟩
⇓-preserve {gc = gc} {pc} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-cast-false {ℓ = ℓ} i L⇓false⟨c⟩ N⇓V V⋎ℓ⟨bc⟩⇓W) =
  let v = ⇓-value N⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢false⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false⟨c⟩ in
  case canonical-const ⊢false⟨c⟩ (⇓-value L⇓false⟨c⟩) of λ where
  (Const-inj _) →  {- g = ⋆ -}
    let pc⋎ℓ≾gc⋎g : l (pc ⋎ ℓ) ≾ (gc ⋎̃ ⋆)
        pc⋎ℓ≾gc⋎g = subst (λ □ → _ ≾ □) (sym (g⋎̃⋆≡⋆ {gc})) ≾-⋆r in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎g N⇓V in
    let ⊢V⋎ℓ⟨bc⟩ = ⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v) in
    let ⟨ Σ₃ , Σ₃⊇Σ₂ , ⊢W , ⊢μ₃ ⟩ = ⇓-preserve ⊢V⋎ℓ⟨bc⟩ ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W in
    ⟨ Σ₃ , ⊇-trans Σ₃⊇Σ₂ (⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ) , ⊢W , ⊢μ₃ ⟩
⇓-preserve (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-fun-cast i L⇓V⟨c⟩ M⇓W elim⇓V′) =
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓W in
  let w = ⇓-value M⇓W in
  case ⇓-value L⇓V⟨c⟩ of λ where
  (V-cast v _) →
    let ⟨ Σ₃ , Σ₃⊇Σ₂ , ⊢V′ , ⊢μ₃ ⟩ = ⇓-preserve (elim-fun-proxy-wt (⊢app (relax-Σ ⊢V⟨c⟩ Σ₂⊇Σ₁) ⊢W) v w i) ⊢μ₂ pc≾gc elim⇓V′ in
    ⟨ Σ₃ , ⊇-trans Σ₃⊇Σ₂ (⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ) , ⊢V′ , ⊢μ₃ ⟩
⇓-preserve (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref-cast i M⇓V⟨c⟩ !V⟨oc⟩⇓W) =
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V⟨c⟩ in
  case canonical-ref ⊢V⟨c⟩ (⇓-value M⇓V⟨c⟩) of λ where
  (Ref-proxy ref i (<:-ty g₂<:g (<:-ref B<:A A<:B))) →
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩ = ⇓-preserve (⊢cast (⊢deref (ref-wt ref))) ⊢μ₁ pc≾gc !V⟨oc⟩⇓W in
    ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢sub ⊢W (stamp-<: B<:A g₂<:g) , ⊢μ₂ ⟩
⇓-preserve (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc (⇓-assign?-cast i L⇓V⟨c⟩ elim⇓W) =
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
  case ⇓-value L⇓V⟨c⟩ of λ where
  (V-cast v _) →
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩ = ⇓-preserve (elim-ref-proxy-wt (⊢assign? ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ)) v i unchecked) ⊢μ₁ pc≾gc elim⇓W in
    ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢W , ⊢μ₂ ⟩
⇓-preserve (⊢assign ⊢L ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-assign-cast i L⇓V⟨c⟩ elim⇓W) =
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩ in
  case ⇓-value L⇓V⟨c⟩ of λ where
  (V-cast v _) →
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩ = ⇓-preserve (elim-ref-proxy-wt (⊢assign ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ) pc′≼ℓ) v i static) ⊢μ₁ pc≾gc elim⇓W in
    ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢W , ⊢μ₂ ⟩
⇓-preserve (⊢sub ⊢M A<:B) ⊢μ pc≾gc M⇓V =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢V , ⊢μ′ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  ⟨ Σ′ , Σ′⊇Σ , ⊢sub ⊢V A<:B , ⊢μ′ ⟩
⇓-preserve (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M⇓V =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢V , ⊢μ′ ⟩ = ⇓-preserve ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M⇓V in
  ⟨ Σ′ , Σ′⊇Σ , ⊢sub-pc ⊢V gc<:gc′ , ⊢μ′ ⟩
