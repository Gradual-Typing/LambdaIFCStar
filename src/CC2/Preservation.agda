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
open import LabelExpr.Security  {- reasoning about security levels of LExpr -}


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
plug-inv (app!□ M A B) (⊢app! ⊢L ⊢M eq) =
  ⟨ _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app! ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) eq) ⟩
plug-inv (app! V □ x A B) (⊢app! ⊢L ⊢M eq) =
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
plug-inv (if!□ _ M N) (⊢if! ⊢L ⊢M ⊢N eq) =
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
{- Protection -}
pres vc ⊢PC (⊢prot {v = vc′} ⊢M ⊢PC′ x eq) ⊢μ (prot-ctx M→N) =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩  = pres vc′ ⊢PC′ ⊢M ⊢μ M→N in
  ⟨ Σ′ , Σ′⊇Σ , ⊢prot ⊢M′ ⊢PC′ x eq , ⊢μ′ ⟩
pres {Σ} vc ⊢PC (⊢prot ⊢V ⊢PC′ x refl) ⊢μ (prot-val v) =
  ⟨ Σ , ⊇-refl Σ , ⊢value-pc (stamp-val-wt v ⊢V) (stamp-val-value v ⊢V) , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ prot-blame = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ prot-blame-pc = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢V⟨c⟩ ⊢μ (cast v V⟨c⟩→M) =
  ⟨ Σ , ⊇-refl Σ , cast-pres ⊢V⟨c⟩ V⟨c⟩→M , ⊢μ ⟩
{- Application -}
pres {Σ} vc ⊢PC (⊢app (⊢lam ⊢N) ⊢V eq) ⊢μ (β v vc†)
  rewrite uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ ,
    ⊢prot (substitution-pres ⊢N (⊢value-pc ⊢V v))
          (stampₑ-wt vc† ⊢PC)
          (≡→≼ (stampₑ-security vc†)) eq , ⊢μ ⟩
pres {Σ} {gc} {A} {PC} vc ⊢PC (⊢app {ℓ = ℓ} (⊢cast (⊢lam ⊢N)) ⊢V eq) ⊢μ
                              (app-cast v vc† 𝓋 ↠PC′ (success vc′) ↠W w)
  rewrite uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ ,
    ⊢prot (⊢cast (substitution-pres ⊢N (⊢value-pc (cast-pres-mult (⊢cast ⊢V) ↠W) w)))
          (preserve-mult (⊢cast (stampₑ-wt vc† ⊢PC)) ↠PC′)
          (stamp-cast-security vc† ⊢PC ↠PC′ vc′) eq , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢app (⊢cast (⊢lam ⊢N)) ⊢V eq) ⊢μ (app-cast v vc† 𝓋 ↠PC′ fail ↠W w) =
  ⟨ Σ , ⊇-refl Σ , ⊢prot-blame-pc , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢app (⊢cast (⊢lam ⊢N)) ⊢V eq) ⊢μ (app-blame v 𝓋 ↠blame) =
  ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢app! (⊢cast (⊢lam ⊢N)) ⊢V eq) ⊢μ (app!-cast v vc† 𝓋 ⊢PC† ↠PC′ (success vc′) ↠W w)
  rewrite eq | uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ ,
    ⊢cast (⊢prot (⊢cast (substitution-pres ⊢N (⊢value-pc (cast-pres-mult (⊢cast ⊢V) ↠W) w)))
                 (preserve-mult (⊢cast (⊢cast (stampₑ-wt vc† ⊢PC†))) ↠PC′)
                 (stamp⇒⋆-cast-security vc† ⊢PC† ↠PC′ vc′) refl) , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢app! (⊢cast (⊢lam ⊢N)) ⊢V eq) ⊢μ (app!-cast v vc† 𝓋 ⊢PC† ↠PC′ fail ↠W w)
  rewrite eq =
  ⟨ Σ , ⊇-refl Σ , ⊢cast ⊢prot-blame-pc , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢app! (⊢cast (⊢lam ⊢N)) ⊢V eq) ⊢μ (app!-blame v 𝓋 ↠blame) =
  ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
{- If -}
pres {Σ} vc ⊢PC (⊢if ⊢const ⊢M ⊢N eq) ⊢μ (β-if-true vc†)
  rewrite uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ , ⊢prot ⊢M (stampₑ-wt vc† ⊢PC) (≡→≼ (stampₑ-security vc†)) eq , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢if ⊢const ⊢M ⊢N eq) ⊢μ (β-if-false vc†)
  rewrite uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ , ⊢prot ⊢N (stampₑ-wt vc† ⊢PC) (≡→≼ (stampₑ-security vc†)) eq , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢if (⊢cast ⊢const) ⊢M ⊢N eq) ⊢μ (if-true-cast vc†)
  rewrite uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ , ⊢prot ⊢M (stampₑ-wt vc† ⊢PC) (≡→≼ (stampₑ-security vc†)) eq , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢if (⊢cast ⊢const) ⊢M ⊢N eq) ⊢μ (if-false-cast vc†)
  rewrite uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ , ⊢prot ⊢N (stampₑ-wt vc† ⊢PC) (≡→≼ (stampₑ-security vc†)) eq , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢if! (⊢cast ⊢const) ⊢M ⊢N eq) ⊢μ
                (if!-true-cast vc† 𝓋 ⊢PC† ↠PC′ (success vc′))
  rewrite eq | uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ ,
    ⊢cast (⊢prot ⊢M (preserve-mult (⊢cast (stampₑ-wt vc† ⊢PC†)) ↠PC′)
                 (≡→≼ (stamp⇒⋆-security vc† ⊢PC† ↠PC′ vc′)) refl), ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢if! (⊢cast ⊢const) ⊢M ⊢N eq) ⊢μ
                (if!-true-cast vc† 𝓋 ⊢PC† ↠PC′ fail)
  rewrite eq =
  ⟨ Σ , ⊇-refl Σ , ⊢cast ⊢prot-blame-pc , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢if! (⊢cast ⊢const) ⊢M ⊢N eq) ⊢μ
                (if!-false-cast vc† 𝓋 ⊢PC† ↠PC′ (success vc′))
  rewrite eq | uniq-LVal vc vc† =
  ⟨ Σ , ⊇-refl Σ ,
    ⊢cast (⊢prot ⊢N (preserve-mult (⊢cast (stampₑ-wt vc† ⊢PC†)) ↠PC′)
                 (≡→≼ (stamp⇒⋆-security vc† ⊢PC† ↠PC′ vc′)) refl), ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢if! (⊢cast ⊢const) ⊢M ⊢N eq) ⊢μ
                (if!-false-cast vc† 𝓋 ⊢PC† ↠PC′ fail)
  rewrite eq =
  ⟨ Σ , ⊇-refl Σ , ⊢cast ⊢prot-blame-pc , ⊢μ ⟩
pres {Σ} vc ⊢PC (⊢let ⊢V ⊢N) ⊢μ (β-let v) =
  ⟨ Σ , ⊇-refl Σ , substitution-pres ⊢N (⊢value-pc ⊢V v) , ⊢μ ⟩
{- Reference creation -}
pres {Σ} vc ⊢PC (⊢ref {T = T} ⊢V _) ⊢μ (ref {ℓ} {V} {n} v fresh) =
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , ⊇-fresh (a⟦ ℓ ⟧ n) T ⊢μ fresh ,
    ⊢addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) , ⊢μ-new (⊢value-pc ⊢V v) v ⊢μ fresh ⟩
pres {Σ} vc ⊢PC (⊢ref? {T = T} ⊢V) ⊢μ (ref? {ℓ} {V} {n} v fresh ↠PC′ vc′) =
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , ⊇-fresh (a⟦ ℓ ⟧ n) T ⊢μ fresh ,
    ⊢addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) , ⊢μ-new (⊢value-pc ⊢V v) v ⊢μ fresh ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ (ref?-blame _ _) = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
{- Assignment -}
pres {Σ} vc ⊢PC (⊢assign (⊢addr hit) ⊢V _ _) ⊢μ (β-assign v) =
  ⟨ Σ , ⊇-refl Σ , ⊢const , ⊢μ-update (⊢value-pc ⊢V v) v ⊢μ hit ⟩
pres {Σ} vc ⊢PC (⊢assign (⊢cast (⊢addr hit)) ⊢V _ _) ⊢μ (assign-cast v 𝓋 ↠W w) =
  let ⊢W = cast-pres-mult (⊢cast ⊢V) ↠W in
  ⟨ Σ , ⊇-refl Σ , ⊢const , ⊢μ-update (⊢value-pc ⊢W w) w ⊢μ hit ⟩
pres {Σ} vc ⊢PC (⊢assign? (⊢addr hit) ⊢V) ⊢μ (β-assign? v vc† ⊢PC† ↠PC′ vc′) =
  ⟨ Σ , ⊇-refl Σ , ⊢const , ⊢μ-update (⊢value-pc ⊢V v) v ⊢μ hit ⟩
pres {Σ} vc ⊢PC (⊢assign? (⊢cast (⊢addr hit)) ⊢V) ⊢μ
                (assign?-cast v vc† 𝓋 ⊢PC† ↠PC′ vc′ ↠W w) =
  let ⊢W = cast-pres-mult (⊢cast ⊢V) ↠W in
  ⟨ Σ , ⊇-refl Σ , ⊢const , ⊢μ-update (⊢value-pc ⊢W w) w ⊢μ hit ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ (assign-blame               _ _ _) = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ (assign?-blame            _ _ _ _) = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ (assign?-cast-blame-pc  _ _ _ _ _) = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
pres {Σ} vc ⊢PC ⊢M ⊢μ (assign?-cast-blame _ _ _ _ _ _ _) = ⟨ Σ , ⊇-refl Σ , ⊢blame , ⊢μ ⟩
{-------------------------------------------}
pres vc ⊢PC ⊢M ⊢μ (deref x) = {!!}
pres vc ⊢PC ⊢M ⊢μ (deref-cast 𝓋 x) = {!!}
