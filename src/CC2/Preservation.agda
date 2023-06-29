module CC2.Preservation where

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
open import CC2.Statics
open import CC2.Reduction
open import CC2.HeapTyping

open import CC2.SubstPreserve using (substitution-pres)

{- Plug inversion -}
plug-inv : ∀ {Σ gc ℓv M A} (F : Frame)
  → [] ; Σ ; gc ; ℓv ⊢ plug M F ⇐ A
    -------------------------------------------------------------
  → ∃[ B ] ([] ; Σ ; gc ; ℓv ⊢ M  ⇐ B) ×
       (∀ {Σ′ M′} → [] ; Σ′ ; gc ; ℓv ⊢ M′ ⇐ B
                  → Σ′ ⊇ Σ
                  → [] ; Σ′ ; gc ; ℓv ⊢ plug M′ F ⇐ A)
plug-inv (app□ M A B _) (⊢app ⊢L ⊢M eq) =
  ⟨ _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) eq) ⟩
plug-inv (app V □ x A B _) (⊢app ⊢L ⊢M eq) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢app (relax-Σ ⊢L Σ′⊇Σ) ⊢M′ eq) ⟩
plug-inv (app!□ M A B x) (⊢app! ⊢L ⊢M eq) =
  ⟨ _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app! ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) eq) ⟩
plug-inv (app! V □ x A B x₁) (⊢app! ⊢L ⊢M eq) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢app! (relax-Σ ⊢L Σ′⊇Σ) ⊢M′ eq) ⟩
plug-inv ref⟦ ℓ ⟧□ (⊢ref ⊢M x) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢ref ⊢M′ x) ⟩
plug-inv (ref?⟦ ℓ ⟧□ p) (⊢ref? ⊢M) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢ref? ⊢M′) ⟩
plug-inv (!□ A g) (⊢deref ⊢M eq) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢deref ⊢M′ eq) ⟩
plug-inv (assign□ M _ ℓ̂ ℓ) (⊢assign ⊢L ⊢M x y) =
  ⟨ _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) x y) ⟩
plug-inv (assign V □ _ _ ℓ̂ ℓ) (⊢assign ⊢L ⊢M x y) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢assign (relax-Σ ⊢L Σ′⊇Σ) ⊢M′ x y) ⟩
plug-inv (assign?□ M x ĝ g x₁) (⊢assign? ⊢L ⊢M) =
  ⟨ _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign? ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inv (assign? V □ x x₁ ĝ g x₂) (⊢assign? ⊢L ⊢M) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢assign? (relax-Σ ⊢L Σ′⊇Σ) ⊢M′) ⟩
plug-inv (let□ _ _) (⊢let ⊢M ⊢N) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢let ⊢M′ (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inv (if□ _ _ M N) (⊢if ⊢L ⊢M ⊢N eq) =
  ⟨ _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢if ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ) eq) ⟩
plug-inv (if!□ _ _ M N) (⊢if! ⊢L ⊢M ⊢N eq) =
  ⟨ _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢if! ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ) eq) ⟩
plug-inv □⟨ c ⟩ (⊢cast ⊢M) =
  ⟨ _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast ⊢M′) ⟩


pres : ∀ {Σ gc A} {PC M N μ μ′}
  → (vc : LVal PC)
  → ⊢ PC ⇐ gc
  → let ℓv = ∥ PC ∥ vc in
     [] ; Σ ; gc ; ℓv ⊢ M ⇐ A
  → Σ ⊢ μ
  → M ∣ μ ∣ PC —→ N ∣ μ′
    ------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; ℓv ⊢ N ⇐ A) × (Σ′ ⊢ μ′)
pres vc ⊢PC ⊢plug ⊢μ (ξ {F = F} M→N) =
  let ⟨ B , ⊢M , wt-plug ⟩ = plug-inv F ⊢plug
      ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩  = pres vc ⊢PC ⊢M ⊢μ M→N in
  ⟨ Σ′ , Σ′⊇Σ , wt-plug ⊢M′ Σ′⊇Σ , ⊢μ′ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ ξ-blame = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres vc ⊢PC (⊢prot {v = vc′} ⊢M ⊢PC′ x eq) ⊢μ (prot-ctx M→N) =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩  = pres vc′ ⊢PC′ ⊢M ⊢μ M→N in
  ⟨ Σ′ , Σ′⊇Σ , ⊢prot ⊢M′ ⊢PC′ x eq , ⊢μ′ ⟩
pres {Σ} vc ⊢PC (⊢prot ⊢V ⊢PC′ x refl) ⊢μ (prot-val v) =
  ⟨ Σ , ⊇-refl Σ , ⊢value-pc (stamp-val-wt v ⊢V) (stamp-val-value v ⊢V) , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ prot-blame = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ prot-blame-pc = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ (cast v V⟨c⟩→M) = {!!}
pres {Σ} vc ⊢PC (⊢app (⊢lam ⊢N) ⊢V eq) ⊢μ (β v vc†) =
  ⟨ Σ , ⊇-refl Σ , ⊢prot (substitution-pres ⊢N (⊢value-pc ⊢V v)) (stampₑ-wt vc† ⊢PC) {!!} eq , ⊢μ ⟩
pres vc ⊢PC ⊢M _ _ = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-app! v vc₁ x x₁ r) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (app-cast v vc₁ 𝓋 x r x₁ x₂) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (app-blame v 𝓋 x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (app!-cast v vc₁ 𝓋 x x₁ r x₂ x₃) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (app!-blame v 𝓋 x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-if-true v) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-if-false v) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-if!-true v x x₁ r) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-if!-false v x x₁ r) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (if-true-cast v) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (if-false-cast v) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (if!-true-cast v 𝓋 x x₁ x₂ r) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (if!-false-cast v 𝓋 x x₁ x₂ r) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-let x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (ref v x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (ref? v x x₁ x₂) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (ref?-blame v x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (deref x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (deref-cast 𝓋 x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-assign v) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (assign-cast v 𝓋 x w) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (assign-blame v 𝓋 x) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (β-assign? v vc₁ x x₁ x₂) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (assign?-blame v vc₁ x x₁) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (assign?-cast v vc₁ 𝓋 x x₁ x₂ x₃ w) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (assign?-cast-blame-pc v vc₁ 𝓋 x x₁) = {!!}
-- pres vc ⊢PC ⊢M ⊢μ (assign?-cast-blame v vc₁ 𝓋 x x₁ x₂ x₃) = {!!}
