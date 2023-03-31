module CC2.TypeSafety where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC2.CCStatics
open import CC2.Reduction

open import CC2.HeapTyping    public
open import CC2.WellTyped     public
open import CC2.SubstPreserve public

data Progress (M : Term) (μ : Heap) (pc : StaticLabel) : Set where
  step : ∀ {N μ′}
    → M ∣ μ ∣ pc —→ N ∣ μ′
      ----------------------------- Step
    → Progress M μ pc

  done : Value M
      ----------------------- Done
    → Progress M μ pc

  err : Err M
      ----------------------- Error
    → Progress M μ pc

progress : ∀ {Σ gc A} pc M → [] ; Σ ; gc ; pc ⊢ M ⦂ A → ∀ μ → Σ ⊢ μ → Progress M μ pc
progress pc ($ k of ℓ) ⊢const μ ⊢μ = done V-const
progress pc (addr a of ℓ) (⊢addr _) μ ⊢μ = done V-addr
progress pc (` x) (⊢var ())
progress pc (ƛ⟦ _ ⟧ A ˙ N of ℓ) (⊢lam ⊢M) μ ⊢μ = done V-ƛ
progress pc (app L M) (⊢app ⊢L ⊢M _ _) μ ⊢μ = step app-static
progress pc (app? L M p) (⊢app? ⊢L ⊢M) μ ⊢μ =
  case progress pc L ⊢L μ ⊢μ of λ where
  (step L→L′) → step (ξ {F = app?□ M p} L→L′)
  (done v) →
    case canonical-fun ⊢L v of λ where
    (Fun-ƛ _ (<:-ty () _))
    (Fun-proxy f (I-fun (cast (⟦ l ℓᶜ ⟧ A ⇒ B of l ℓ) _ _ _) I-label I-label)
      (<:-ty <:-⋆ (<:-fun <:-⋆ _ _))) →
        case nsu? pc ℓ ℓᶜ of λ where
        (yes nsu-yes) → step (app?-ok (fun-is-value f) nsu-yes)
        (no  nsu-no)  → step (app?-fail (fun-is-value f) nsu-no)
  (err (E-error {e})) → step (ξ-err {F = app?□ M p} {e = e})
progress pc (app✓ L M) (⊢app✓ ⊢L ⊢M _ _) μ ⊢μ =
  case progress pc L ⊢L μ ⊢μ of λ where
  (step L→L′) → step (ξ {F = app✓□ M} L→L′)
  (done v) →
    case progress pc M ⊢M μ ⊢μ of λ where
    (step M→M′) → step (ξ {F = (app✓ L □) v} M→M′)
    (done w) →
      case canonical-fun ⊢L v of λ where
      (Fun-ƛ _ _) → step (β w)
      (Fun-proxy f (I-fun (cast (⟦ l _ ⟧ _ ⇒ _ of l _) (⟦ l _ ⟧ _ ⇒ _ of l _) _ _) I-label I-label)
        (<:-ty (<:-l _) (<:-fun (<:-l _) _ _))) →
        step (fun-cast (fun-is-value f) w)
    (err (E-error {e})) → step (ξ-err {F = (app✓ L □) v} {e = e})
  (err (E-error {e})) → step (ξ-err {F = app✓□ M} {e = e})
progress pc (if L A M N) (⊢if ⊢L ⊢M ⊢N) μ ⊢μ =
  case progress pc L ⊢L μ ⊢μ of λ where
  (step L→L′) → step (ξ {F = if□ A M N} L→L′)
  (done v) →
    case canonical-const ⊢L v of λ where
    (Const-base {𝔹} {true} _)  → step β-if-true
    (Const-base {𝔹} {false} _) → step β-if-false
  (err (E-error {e})) → step (ξ-err {F = if□ A M N} {e = e})
progress pc (if⋆ L A M N) (⊢if⋆ ⊢L ⊢M ⊢N) μ ⊢μ =
  case progress pc L ⊢L μ ⊢μ of λ where
  (step L→L′) → step (ξ {F = if⋆□ A M N} L→L′)
  (done v) →
    case canonical-const ⊢L v of λ where
    (Const-inj {𝔹} {true}  {c = cast (` ι of l ℓ′) (` ι of ⋆) _ _} _) → step β-if⋆-true
    (Const-inj {𝔹} {false} {c = cast (` ι of l ℓ′) (` ι of ⋆) _ _} _) → step β-if⋆-false
  (err (E-error {e})) → step (ξ-err {F = if⋆□ A M N} {e = e})
progress pc (`let M N) (⊢let ⊢M ⊢N) μ ⊢μ =
  case progress pc M ⊢M μ ⊢μ of λ where
  (step M→M′) → step (ξ {F = let□ N} M→M′)
  (done v) → step (β-let v)
  (err (E-error {e})) → step (ξ-err {F = let□ N} {e = e})
progress pc (ref⟦ ℓ ⟧ M) (⊢ref ⊢M pc′≼ℓ) μ ⊢μ =
  step ref-static
progress pc (ref?⟦ ℓ ⟧ M p) (⊢ref? ⊢M) μ ⊢μ =
  case pc ≼? ℓ of λ where
  (yes pc≼ℓ) → step (ref?-ok pc≼ℓ)
  (no  pc⋠ℓ) → step (ref?-fail pc⋠ℓ)
progress {Σ} pc (ref✓⟦ ℓ ⟧ M) (⊢ref✓ ⊢M pc≼ℓ) μ ⊢μ =
  case progress pc M ⊢M μ ⊢μ of λ where
    (step M→M′) → step (ξ {F = ref✓⟦ ℓ ⟧□} M→M′)
    (done v) →
      let ⟨ n , fresh ⟩ = gen-fresh μ in step (ref v fresh)
    (err (E-error {e})) →
      step (ξ-err {F = ref✓⟦ ℓ ⟧□} {e = e})
progress pc (! M) (⊢deref ⊢M) μ ⊢μ =
  case progress pc M ⊢M μ ⊢μ of λ where
  (step M→M′) → step (ξ {F = !□} M→M′)
  (done v) →
    case canonical-ref ⊢M v of λ where
    (Ref-addr {n = n} {ℓ₁ = ℓ₁} eq _) →
      let ⟨ wf , V₁ , v₁ , eq , ⊢V₁ ⟩ = ⊢μ n ℓ₁ eq in
      step (deref {v = v₁} eq)
    (Ref-proxy r (I-ref (cast (Ref (_ of l _) of l _) _ _ _) I-label I-label) _) →
      step (deref-cast (ref-is-value r))
  (err (E-error {e})) → step (ξ-err {F = !□} {e = e})
progress pc (assign L M) (⊢assign ⊢L ⊢M ℓ≼ℓ̂ pc′≼ℓ̂) μ ⊢μ =
  step assign-static
progress pc (assign? L M p) (⊢assign? ⊢L ⊢M) μ ⊢μ =
  case progress pc L ⊢L μ ⊢μ of λ where
  (step L→L′) → step (ξ {F = assign?□ M p} L→L′)
  (done v) →
    case canonical-ref ⊢L v of λ where
    (Ref-addr {n = n} {ℓ₁ = ℓ₁} eq (<:-ty () _))
    (Ref-proxy r (I-ref (cast (Ref (T of l ℓ̂) of l ℓ) _ _ _) I-label I-label)
      (<:-ty <:-⋆ (<:-ref (<:-ty <:-⋆ _) _))) →
        case nsu? pc ℓ ℓ̂ of λ where
        (yes nsu-yes) → step (assign?-ok (ref-is-value r) nsu-yes)
        (no  nsu-no)  → step (assign?-fail (ref-is-value r) nsu-no)
  (err (E-error {e})) → step (ξ-err {F = assign?□ M p} {e = e})
progress pc (assign✓ L M) (⊢assign✓ ⊢L ⊢M ℓ≼ℓ̂ pc≼ℓ̂) μ ⊢μ =
  case progress pc L ⊢L μ ⊢μ of λ where
  (step L→L′) → step (ξ {F = assign✓□ M} L→L′)
  (done v) →
    case progress pc M ⊢M μ ⊢μ of λ where
    (step M→M′) → step (ξ {F = (assign✓ L □) v} M→M′)
    (done w) →
      case canonical-ref ⊢L v of λ where
      (Ref-addr eq _) → step (β-assign w)
      (Ref-proxy r i _) →
        case i of λ where
        (I-ref _ I-label I-label) → step (assign-cast (ref-is-value r) w i)
    (err (E-error {e})) → step (ξ-err {F = (assign✓ L □) v} {e = e})
  (err (E-error {e})) → step (ξ-err {F = assign✓□ M} {e = e})
progress pc (prot g ℓ M) (⊢prot ⊢M _) μ ⊢μ =
  case progress (pc ⋎ ℓ) M ⊢M μ ⊢μ of λ where
  (step M→N) → step (prot-ctx M→N)
  (done v) → step (prot-val v)
  (err E-error) → step prot-err
progress pc (M ⟨ c ⟩) (⊢cast ⊢M) μ ⊢μ =
  case progress pc M ⊢M μ ⊢μ of λ where
  (step M→M′) → step (ξ {F = □⟨ c ⟩} M→M′)
  (done v) →
    case active-or-inert c of λ where
    (inj₁ a) →
      case applycast-progress (⊢value-pc ⊢M v) v a of λ where
      ⟨ N , M⟨c⟩↝N ⟩ → step (cast v a M⟨c⟩↝N)
    (inj₂ i) → done (V-cast v i)
  (err (E-error {e})) → step (ξ-err {F = □⟨ c ⟩} {e = e})
progress pc (blame e p) ⊢blame μ ⊢μ = err E-error
progress pc M (⊢sub ⊢M _) μ ⊢μ = progress pc M ⊢M μ ⊢μ
progress pc M (⊢sub-pc ⊢M _) μ ⊢μ = progress pc M ⊢M μ ⊢μ


preserve : ∀ {Σ gc pc M M′ A μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → M ∣ μ ∣ pc —→ M′ ∣ μ′
    ---------------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; pc ⊢ M′ ⦂ A) × (Σ′ ⊢ μ′)
preserve ⊢plug ⊢μ pc≾gc (ξ {F = F} M→M′) =
  let ⟨ gc′ , B , pc≾gc′ , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug pc≾gc
      ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩  = preserve ⊢M ⊢μ pc≾gc′ M→M′ in
  ⟨ Σ′ , Σ′⊇Σ , wt-plug ⊢M′ Σ′⊇Σ , ⊢μ′ ⟩
preserve {Σ} ⊢M ⊢μ pc≾gc ξ-err = ⟨ Σ , ⊇-refl Σ , ⊢err , ⊢μ ⟩
preserve {Σ} (⊢prot ⊢V _) ⊢μ pc≾gc (prot-val v) =
  ⟨ Σ , ⊇-refl Σ , ⊢value-pc (stamp-val-wt ⊢V v) (stamp-val-value v) , ⊢μ ⟩
preserve (⊢prot ⊢M pc~g) ⊢μ pc≾gc (prot-ctx M→M′) =
  let pc≾g = proj₁ (~ₗ→≾ pc~g) in
  let pc⋎ℓ≾g⋎ℓ = consis-join-≾ pc≾g ≾-refl in
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ pc⋎ℓ≾g⋎ℓ M→M′ in
  ⟨ Σ′ , Σ′⊇Σ , ⊢prot ⊢M′ pc~g , ⊢μ′ ⟩
preserve {Σ} ⊢M ⊢μ pc≾gc prot-err = ⟨ Σ , ⊇-refl Σ , ⊢err , ⊢μ ⟩
preserve {Σ} (⊢app ⊢L ⊢M pc′≼ℓᶜ ℓ≼ℓᶜ) ⊢μ (≾-l pc≼pc′) app-static =
  ⟨ Σ , ⊇-refl Σ , ⊢app✓ ⊢L ⊢M (≼-trans pc≼pc′ pc′≼ℓᶜ) ℓ≼ℓᶜ , ⊢μ ⟩
preserve {Σ} (⊢app✓ ⊢V ⊢M pc≼ℓᶜ′ ℓ′≼ℓᶜ′) ⊢μ pc≾gc (β v) =
  case canonical-fun ⊢V V-ƛ of λ where
  (Fun-ƛ ⊢N (<:-ty (<:-l ℓ≼ℓ′) (<:-fun (<:-l ℓᶜ′≼ℓᶜ) A<:A′ B′<:B))) →
    let pc≼ℓᶜ = ≼-trans pc≼ℓᶜ′ ℓᶜ′≼ℓᶜ in
    let ℓ≼ℓᶜ = ≼-trans (≼-trans ℓ≼ℓ′ ℓ′≼ℓᶜ′) ℓᶜ′≼ℓᶜ in
    let pc⋎ℓ≼ℓᶜ = subst (λ □ → _ ⋎ _ ≼ □) ℓ⋎ℓ≡ℓ (join-≼′ pc≼ℓᶜ ℓ≼ℓᶜ) in
    ⟨ Σ , ⊇-refl Σ ,
      ⊢sub (⊢prot (substitution-pres (⊢sub-pc ⊢N (<:-l pc⋎ℓ≼ℓᶜ)) (⊢value-pc (⊢sub ⊢M A<:A′) v)) ~ₗ-refl)
           (stamp-<: B′<:B (<:-l ℓ≼ℓ′)) , ⊢μ ⟩
preserve {Σ} (⊢if ⊢L ⊢M ⊢N) ⊢μ (≾-l pc≼pc′) (β-if-true {ℓ = ℓ}) =
  case const-label-≼ ⊢L of λ where
  ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
    ⟨ Σ , ⊇-refl Σ ,
      ⊢sub (⊢prot (⊢sub-pc ⊢M (<:-l (join-≼′ pc≼pc′ ℓ≼ℓ′))) ~ₗ-refl) (stamp-<: <:-refl (<:-l ℓ≼ℓ′)) , ⊢μ ⟩
preserve {Σ} (⊢if ⊢L ⊢M ⊢N) ⊢μ (≾-l pc≼pc′) (β-if-false {ℓ = ℓ}) =
  case const-label-≼ ⊢L of λ where
  ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
    ⟨ Σ , ⊇-refl Σ ,
      ⊢sub (⊢prot (⊢sub-pc ⊢N (<:-l (join-≼′ pc≼pc′ ℓ≼ℓ′))) ~ₗ-refl) (stamp-<: <:-refl (<:-l ℓ≼ℓ′)) , ⊢μ ⟩
preserve {Σ} (⊢let ⊢V ⊢N) ⊢μ pc≾gc (β-let v) =
  ⟨ Σ , ⊇-refl Σ , substitution-pres ⊢N (⊢value-pc ⊢V v) , ⊢μ ⟩
preserve {Σ} (⊢ref ⊢M pc′≼ℓ) ⊢μ (≾-l pc≼pc′) ref-static =
  ⟨ Σ , ⊇-refl Σ , ⊢ref✓ ⊢M (≼-trans pc≼pc′ pc′≼ℓ) , ⊢μ ⟩
preserve {Σ} (⊢ref✓ {T = T} {ℓ} ⊢V pc≼ℓ) ⊢μ pc≾gc (ref {n = n} {.ℓ} v fresh) =
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , ⊇-fresh (a⟦ ℓ ⟧ n) T ⊢μ fresh ,
    ⊢addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) , ⊢μ-new (⊢value-pc ⊢V v) v ⊢μ fresh ⟩
preserve {Σ} (⊢ref? ⊢M) ⊢μ pc≾gc (ref?-ok pc≼ℓ) =
  ⟨ Σ , ⊇-refl Σ , ⊢ref✓ ⊢M pc≼ℓ , ⊢μ ⟩
preserve {Σ} (⊢ref? ⊢M) ⊢μ pc≾gc (ref?-fail pc⋠ℓ) =
  ⟨ Σ , ⊇-refl Σ , ⊢err , ⊢μ ⟩
preserve {Σ} (⊢deref ⊢a) ⊢μ pc≾gc (deref {ℓ = ℓ} {ℓ₁} eq) =
  case canonical-ref ⊢a V-addr of λ where
  (Ref-addr {n = n} {g = l ℓ′} {ℓ₁ = ℓ₁} eq₁ (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
    case <:-antisym A′<:A A<:A′ of λ where
    refl →
      let ⟨ wf , V₁ , v₁ , eq′ , ⊢V₁ ⟩ = ⊢μ n ℓ₁ eq₁ in
      case trans (sym eq) eq′ of λ where
      refl →
        let leq : ℓ₁ ⋎ (ℓ₁ ⋎ ℓ) ≼ ℓ₁ ⋎ ℓ′
            leq = subst (λ □ → □ ≼ _) (sym ℓ₁⋎[ℓ₁⋎ℓ]≡ℓ₁⋎ℓ) (join-≼′ ≼-refl ℓ≼ℓ′) in
        ⟨ Σ , ⊇-refl Σ ,  ⊢sub (⊢prot (⊢value-pc ⊢V₁ v₁) ~ₗ-refl) (<:-ty (<:-l leq) <:ᵣ-refl) , ⊢μ ⟩
preserve {Σ} (⊢assign ⊢L ⊢M ℓ≼ℓ̂ pc′≼ℓ̂) ⊢μ (≾-l pc≼pc′) assign-static =
  ⟨ Σ , ⊇-refl Σ , ⊢assign✓ ⊢L ⊢M ℓ≼ℓ̂ (≼-trans pc≼pc′ pc′≼ℓ̂) , ⊢μ ⟩
preserve {Σ} (⊢assign✓ {ℓ = ℓ′} ⊢a ⊢V _ pc≼ℓ′) ⊢μ pc≾gc (β-assign {ℓ = ℓ} {ℓ₁} v) =
 case canonical-ref ⊢a V-addr of λ where
 (Ref-addr eq (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
   case <:-antisym A′<:A A<:A′ of λ where
   refl → ⟨ Σ , ⊇-refl Σ , ⊢const , ⊢μ-update (⊢value-pc ⊢V v) v ⊢μ eq ⟩
preserve {Σ} (⊢cast ⊢V) ⊢μ pc≾gc (cast v a V⟨c⟩↝M) =
  ⟨ Σ , ⊇-refl Σ , applycast-pres (⊢value-pc ⊢V v) v a V⟨c⟩↝M , ⊢μ ⟩
-- preserve {Σ} {gc} {pc} (⊢if {A = A} {L} {M} {N} ⊢L ⊢M ⊢N) ⊢μ pc≾gc (if-cast-true i) with i
-- ... | (I-base-inj (cast (` Bool of l ℓ′) (` Bool of ⋆) p _)) =
--   case canonical-const ⊢L (V-cast V-const i) of λ where
--   (Const-inj {ℓ = ℓ} ℓ≼ℓ′) →
--     let ⊢M† : [] ; Σ ; ⋆ ; pc ⋎ ℓ ⊢ M ⦂ A
--         ⊢M† = subst (λ □ → [] ; Σ ; □ ; pc ⋎ ℓ ⊢ M ⦂ A) g⋎̃⋆≡⋆ ⊢M in
--     let A⋎ℓ<:A⋎ℓ′ = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
--     ⟨ Σ , ⊇-refl Σ , ⊢cast (⊢sub (⊢prot ⊢M† {!!}) A⋎ℓ<:A⋎ℓ′), ⊢μ ⟩
-- preserve {Σ} {gc} {pc} (⊢if {A = A} {L} {M} {N} ⊢L ⊢M ⊢N) ⊢μ pc≾gc (if-cast-false i) with i
-- ... | (I-base-inj (cast (` Bool of l ℓ′) (` Bool of ⋆) p _)) =
--   case canonical-const ⊢L (V-cast V-const i) of λ where
--   (Const-inj {ℓ = ℓ} ℓ≼ℓ′) →
--     let ⊢N† : [] ; Σ ; ⋆ ; pc ⋎ ℓ ⊢ N ⦂ A
--         ⊢N† = subst (λ □ → [] ; Σ ; □ ; pc ⋎ ℓ ⊢ N ⦂ A) g⋎̃⋆≡⋆ (⊢N {pc ⋎ ℓ}) in
--     let A⋎ℓ<:A⋎ℓ′ = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
--     ⟨ Σ , ⊇-refl Σ , ⊢cast (⊢sub (⊢prot ⊢N† {!!}) A⋎ℓ<:A⋎ℓ′) , ⊢μ ⟩
preserve {Σ} {gc} {pc} (⊢app✓ ⊢L ⊢M pc≼ℓᶜ ℓ≼ℓᶜ) ⊢μ pc≾gc (fun-cast {V} {W} {pc = pc} v w) =
  ⟨ Σ , ⊇-refl Σ , {!!} , ⊢μ ⟩
preserve {Σ} (⊢deref {A = A′} ⊢M) ⊢μ pc≾gc (deref-cast v) =
  case canonical-ref ⊢M (V-cast v (I-ref _ I-label I-label)) of λ where
  (Ref-proxy r _ (<:-ty g₂<:g (<:-ref B<:A′ A′<:B))) →
    case <:-antisym B<:A′ A′<:B of λ where
    refl →
      ⟨ Σ , ⊇-refl Σ ,
        ⊢sub (⊢cast (⊢deref (ref-wt r))) (stamp-<: <:-refl g₂<:g) , ⊢μ ⟩
preserve {Σ} {gc} {pc} (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc (assign?-ok {c~ = c~} v ⟨ pc≼ℓ̂ , ℓ≼ℓ̂ ⟩) =
  case canonical-ref ⊢L (V-cast v (I-ref _ I-label I-label)) of λ where
  (Ref-proxy r _ (<:-ty g<:g′ (<:-ref A<:B B<:A))) →
    case ⟨ c~ , g<:g′ , <:-antisym A<:B B<:A ⟩ of λ where
    ⟨ ~-ty ~⋆ (~-ref (~-ty ~⋆ _)) , <:-⋆ , refl ⟩ →
      ⟨ Σ , ⊇-refl Σ , ⊢assign✓ (ref-wt r) (⊢cast ⊢M) ℓ≼ℓ̂ pc≼ℓ̂ , ⊢μ ⟩
preserve {Σ} {gc} {pc} (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc (assign?-fail v nsu-no) =
  ⟨ Σ , ⊇-refl Σ , ⊢err , ⊢μ ⟩
preserve {Σ} {gc} (⊢assign✓ ⊢L ⊢M ℓ≼ℓ̂ pc′≼ℓ) ⊢μ pc≾gc (assign-cast v w i)
  with i
... | I-ref (cast _ _ _ c~) I-label I-label =
  case canonical-ref ⊢L (V-cast v i) of λ where
  (Ref-proxy r _ (<:-ty ℓ<:ℓ′ (<:-ref A<:B B<:A))) →
    case ⟨ c~ , <:-antisym A<:B B<:A ⟩ of λ where
    ⟨ ~-ty l~ (~-ref (~-ty l~ _)) , refl ⟩ →
      ⟨ Σ , ⊇-refl Σ , ⊢assign✓ (⊢sub (ref-wt r) (<:-ty ℓ<:ℓ′ <:ᵣ-refl)) (⊢cast ⊢M) ℓ≼ℓ̂ pc′≼ℓ , ⊢μ ⟩
preserve (⊢sub ⊢M A<:B) ⊢μ pc≾gc M→M′ =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ pc≾gc M→M′ in
  ⟨ Σ′ , Σ′⊇Σ , ⊢sub ⊢M′ A<:B , ⊢μ′ ⟩
preserve (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M→M′ =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M→M′ in
  ⟨ Σ′ , Σ′⊇Σ , ⊢sub-pc ⊢M′ gc<:gc′ , ⊢μ′ ⟩
