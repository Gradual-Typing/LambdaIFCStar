module CC2.WellTyped where

open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC2.CCStatics
open import CC2.HeapTyping
open import CC2.Frame
open import CC2.ProxyElimination


{- Function and reference predicates respect type -}
fun-wt : ∀ {Σ V gc gc′ pc A B g}
  → Fun V Σ (⟦ gc′ ⟧ A ⇒ B of g)
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ⟦ gc′ ⟧ A ⇒ B of g
fun-wt (Fun-ƛ {Σ} ⊢N sub)    = ⊢sub (⊢lam ⊢N) sub
fun-wt (Fun-proxy fun i sub) = ⊢sub (⊢cast (fun-wt fun)) sub

ref-wt : ∀ {Σ V gc pc A g}
  → Reference V Σ (Ref A of g)
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
ref-wt (Ref-addr eq sub)     = ⊢sub (⊢addr eq) sub
ref-wt (Ref-proxy r i sub) = ⊢sub (⊢cast (ref-wt r)) sub


{- Value stamping is well-typed -}
stamp-val-wt : ∀ {Σ gc pc V A ℓ}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ A
  → (v : Value V)
  → [] ; Σ ; gc ; pc ⊢ stamp-val V v ℓ ⦂ stamp A (l ℓ)
stamp-val-wt (⊢addr eq) V-addr = ⊢addr eq
stamp-val-wt (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
stamp-val-wt ⊢const V-const = ⊢const
stamp-val-wt (⊢cast ⊢V) (V-cast v i) = ⊢cast (stamp-val-wt ⊢V v)
stamp-val-wt (⊢sub ⊢V A<:B) v = ⊢sub (stamp-val-wt ⊢V v) (stamp-<: A<:B <:ₗ-refl)
stamp-val-wt (⊢sub-pc ⊢V gc<:gc′) v = ⊢sub-pc (stamp-val-wt ⊢V v) gc<:gc′


-- {- Proxy elimination preserves type -}
-- elim-fun-proxy-wt : ∀ {Σ gc pc V W A A′ B C D gc₁ gc₂ g₁ g₂}
--                       {c : Cast ⟦ gc₁ ⟧ A ⇒ B of g₁ ⇒ ⟦ gc₂ ⟧ C ⇒ D of g₂}
--   → [] ; Σ ; gc ; pc ⊢ (V ⟨ c ⟩) · W ⦂ A′
--   → Value V → Value W
--   → (i : Inert c)
--     ---------------------------------------------------
--   → [] ; Σ ; gc ; pc ⊢ elim-fun-proxy V W i pc ⦂ A′
-- elim-fun-proxy-wt {Σ} {gc} {pc} (⊢app ⊢Vc ⊢W) v w i
--  with i
-- ... | I-fun (cast (⟦ l pc₁ ⟧ A ⇒ B of l ℓ₁) (⟦ l pc₂ ⟧ C ⇒ D of g₂) p c~) I-label I-label =
--   case ⟨ canonical-fun ⊢Vc (V-cast v i) , c~ ⟩ of λ where
--   ⟨ Fun-proxy f _ (<:-ty g₂<:g (<:-fun gc⋎g<:pc₂ A₁<:C D<:B₁)) , ~-ty g₁~g₂ (~-fun l~ _ _) ⟩ →
--     -- doing label arithmetic
--     case ⟨ g₁~g₂ , g₂<:g , consis-join-<:ₗ-inv gc⋎g<:pc₂ ⟩ of λ where
--     ⟨ l~ , <:-l g₂≼g , <:-l gc≼pc₂ , <:-l g≼pc₂ ⟩ →
--       let ⊢V = fun-wt {gc = gc} f
--           g₂≼pc₂ = ≼-trans g₂≼g g≼pc₂
--           gc⋎g₂≼pc₂ = subst (λ □ → _ ⋎ _ ≼ □) ℓ⋎ℓ≡ℓ (join-≼′ gc≼pc₂ g₂≼pc₂)
--           ⊢V† = ⊢sub ⊢V (<:-ty <:ₗ-refl (<:-fun (<:-l gc⋎g₂≼pc₂) <:-refl <:-refl)) in
--       ⊢sub (⊢cast (⊢app ⊢V† (⊢cast (⊢sub (⊢value-pc ⊢W w) A₁<:C)))) (stamp-<: D<:B₁ g₂<:g)
-- ... | I-fun (cast (⟦ l pc₁ ⟧ A ⇒ B of l ℓ₁) (⟦ ⋆ ⟧ C ⇒ D of g₂) p c~) I-label I-label
--   with pc ⋎ ℓ₁ ≼? pc₁
-- ...   | yes pc⋎ℓ₁≼pc₁ =
--   case ⟨ canonical-fun ⊢Vc (V-cast v i) , c~ ⟩ of λ where
--   ⟨ Fun-proxy f _ (<:-ty g₂<:g (<:-fun gc⋎g<:⋆ A₁<:C D<:B₁)) , ~-ty g₁~g₂ (~-fun ~⋆ _ _) ⟩ →
--     let ⊢V  = fun-wt {gc = gc} {pc = pc} f
--         ⊢V† = ⊢value-pc {gc′ = l pc} (⊢sub ⊢V (<:-ty <:ₗ-refl (<:-fun (<:-l pc⋎ℓ₁≼pc₁) <:-refl <:-refl))) v in
--       ⊢sub (⊢cast (⊢cast-pc (⊢app ⊢V† (⊢cast (⊢sub (⊢value-pc ⊢W w) A₁<:C))) l~))
--            (stamp-<: D<:B₁ g₂<:g)
-- ...   | no  _ = ⊢err
-- elim-fun-proxy-wt (⊢sub ⊢M A<:B) v w i = ⊢sub (elim-fun-proxy-wt ⊢M v w i) A<:B
-- elim-fun-proxy-wt (⊢sub-pc ⊢M gc<:gc′) v w i = ⊢sub-pc (elim-fun-proxy-wt ⊢M v w i) gc<:gc′

-- elim-ref-proxy-wt : ∀ {Σ gc pc V W A A′ T g}
--                       {c : Cast Ref A of g ⇒ Ref (T of ⋆) of ⋆}
--   → [] ; Σ ; gc ; pc ⊢ (V ⟨ c ⟩) :=? W ⦂ A′
--   → Value V → (i : Inert c) → (pc : StaticLabel)
--     ----------------------------------------------------
--   → [] ; Σ ; gc ; pc ⊢ elim-ref-proxy V W i pc ⦂ A′
-- elim-ref-proxy-wt (⊢assign? ⊢L ⊢M) v i pc
--   with i
-- ... | I-ref (cast (Ref (S of l ℓ̂) of l ℓ) (Ref (T of ⋆) of ⋆) p c~) I-label I-label
--   with ℓ ≼? ℓ̂ | pc ≼? ℓ̂
-- ...   | yes ℓ≼ℓ̂ | yes pc≼ℓ̂  =
--   case canonical-ref ⊢L (V-cast v i) of λ where
--   (Ref-proxy r _ (<:-ty g<:g′ (<:-ref A<:B B<:A))) →
--     case ⟨ c~ , g<:g′ , <:-antisym A<:B B<:A ⟩ of λ where
--     ⟨ ~-ty ~⋆ (~-ref (~-ty ~⋆ _)) , <:-⋆ , refl ⟩ →
--       ⊢assign✓ (ref-wt r) (⊢cast ⊢M) ℓ≼ℓ̂ pc≼ℓ̂
-- ...   | yes  _ | no _ = ⊢err
-- ...   | no  _ | yes _ = ⊢err
-- ...   | no  _ | no _ = ⊢err
-- elim-ref-proxy-wt (⊢sub ⊢M A<:B) v i pc = ⊢sub (elim-ref-proxy-wt ⊢M v i pc) A<:B
-- elim-ref-proxy-wt (⊢sub-pc ⊢M gc<:gc′) v i pc = ⊢sub-pc (elim-ref-proxy-wt ⊢M v i pc) gc<:gc′


{- Plug inversion -}
plug-inversion : ∀ {Σ gc pc M A} {F : Frame}
  → [] ; Σ ; gc ; pc ⊢ plug M F ⦂ A
  → l pc ≾ gc
    -------------------------------------------------------------
  → ∃[ gc′ ] ∃[ B ]
       (l pc ≾ gc′) × ([] ; Σ ; gc′ ; pc ⊢ M ⦂ B) ×
       (∀ {Σ′ M′} → [] ; Σ′ ; gc′ ; pc ⊢ M′ ⦂ B → Σ′ ⊇ Σ → [] ; Σ′ ; gc ; pc ⊢ plug M′ F ⦂ A)
plug-inversion {F = app?□ M p} (⊢app? ⊢L ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app? ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = app✓□ M} (⊢app✓ ⊢L ⊢M pc≼ℓᶜ ℓ≼ℓᶜ) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app✓ ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) pc≼ℓᶜ ℓ≼ℓᶜ) ⟩
plug-inversion {F = (app✓ V □) v} (⊢app✓ ⊢V ⊢M pc≼ℓᶜ ℓ≼ℓᶜ) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢app✓ (relax-Σ ⊢V Σ′⊇Σ) ⊢M′ pc≼ℓᶜ ℓ≼ℓᶜ) ⟩
plug-inversion {F = ref✓⟦ ℓ ⟧□} (⊢ref✓ ⊢M pc≼ℓ) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢ref✓ ⊢M′ pc≼ℓ) ⟩
plug-inversion {F = !□} (⊢deref ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢deref ⊢M′) ⟩
plug-inversion {F = assign?□ M p} (⊢assign? ⊢L ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign? ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = assign✓□ M} (⊢assign✓ ⊢L ⊢M ℓ≼ℓ̂ pc≼ℓ̂) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign✓ ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) ℓ≼ℓ̂ pc≼ℓ̂) ⟩
plug-inversion {F = (assign✓ V □) v} (⊢assign✓ ⊢V ⊢M ℓ≼ℓ̂ pc≼ℓ̂) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢assign✓ (relax-Σ ⊢V Σ′⊇Σ) ⊢M′ ℓ≼ℓ̂ pc≼ℓ̂) ⟩
plug-inversion {F = let□ N} (⊢let ⊢M ⊢N) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢let ⊢M′ (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = if□ A M N} (⊢if ⊢L ⊢M ⊢N) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢if ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = □⟨ c ⟩} (⊢cast ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast ⊢M′) ⟩
plug-inversion {F = cast-pc g □} (⊢cast-pc ⊢M pc~g) _ =
  ⟨ g , _ , proj₁ (~ₗ→≾ pc~g) , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast-pc ⊢M′ pc~g) ⟩
plug-inversion (⊢sub ⊢M A<:B) pc≾gc =
  let ⟨ gc′ , B , pc≾gc′ , ⊢M , wt-plug ⟩ = plug-inversion ⊢M pc≾gc in
  ⟨ gc′ , B , pc≾gc′ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub (wt-plug ⊢M′ Σ′⊇Σ) A<:B) ⟩
plug-inversion (⊢sub-pc ⊢plug gc<:gc′) pc≾gc =
  let ⟨ gc″ , B , pc≾gc″ , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug (≾-<: pc≾gc gc<:gc′) in
  ⟨ gc″ , B , pc≾gc″ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub-pc (wt-plug ⊢M′ Σ′⊇Σ) gc<:gc′) ⟩


{- Applying cast is well-typed -}
open import CC2.ApplyCastWT public
