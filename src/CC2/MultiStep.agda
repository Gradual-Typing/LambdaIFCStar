module CC2.MultiStep where

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
open import CC2.Statics
open import CC2.Reduction
open import CC2.Preservation


{- Multi-step reduction -}
infix  2 _∣_∣_—↠_∣_
infixr 2 _∣_∣_—→⟨_⟩_
infix  3 _∣_∣_∎

data _∣_∣_—↠_∣_ : Term → Heap → LExpr → Term → Heap → Set where

    _∣_∣_∎ : ∀ M μ PC
        -----------------------------------
      → M ∣ μ ∣ PC —↠ M ∣ μ

    _∣_∣_—→⟨_⟩_ : ∀ L μ PC {M N μ′ μ″}
      → L ∣ μ  ∣ PC —→ M ∣ μ′
      → M ∣ μ′ ∣ PC —↠ N ∣ μ″
        -----------------------------------
      → L ∣ μ  ∣ PC —↠ N ∣ μ″


trans-mult : ∀ {M₁ M₂ M₃ μ₁ μ₂ μ₃ pc}
  → M₁ ∣ μ₁ ∣ pc —↠ M₂ ∣ μ₂
  → M₂ ∣ μ₂ ∣ pc —↠ M₃ ∣ μ₃
  → M₁ ∣ μ₁ ∣ pc —↠ M₃ ∣ μ₃
trans-mult (M ∣ μ ∣ pc ∎) (M ∣ μ ∣ pc ∎) = M ∣ μ ∣ pc ∎
trans-mult (M₁ ∣ μ₁ ∣ pc ∎) (M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃) =
  M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃
trans-mult (M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃) (M₃ ∣ μ₃ ∣ pc ∎) =
  M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃
trans-mult (M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ M₂↠M₃)
            (M₃ ∣ μ₃ ∣ pc —→⟨ M₃→M₄ ⟩ M₄↠M₅) =
  M₁ ∣ μ₁ ∣ pc —→⟨ M₁→M₂ ⟩ (trans-mult M₂↠M₃ (M₃ ∣ μ₃ ∣ pc —→⟨ M₃→M₄ ⟩ M₄↠M₅))


plug-cong : ∀ {M N μ μ′ PC}
  → (F : Frame)
  → M ∣ μ ∣ PC —↠ N ∣ μ′
  → plug M F ∣ μ ∣ PC —↠ plug N F ∣ μ′
plug-cong F (_ ∣ _ ∣ _ ∎) = _ ∣ _ ∣ _ ∎
plug-cong F (L ∣ μ ∣ PC —→⟨ L→M ⟩ M↠N) =
  plug L F ∣ μ ∣ PC —→⟨ ξ L→M ⟩ plug-cong F M↠N

prot-ctx-mult : ∀ {M N μ μ′ PC PC′} {A ℓ}
  → (vc′ : LVal PC′)
  → M ∣ μ ∣ PC′ —↠ N ∣ μ′
  → prot PC′ vc′ ℓ M A ∣ μ ∣ PC —↠ prot PC′ vc′ ℓ N A ∣ μ′
prot-ctx-mult vc′ (_ ∣ _ ∣ _ ∎) = _ ∣ _ ∣ _ ∎
prot-ctx-mult {PC = PC} {PC′} vc′ (L ∣ μ ∣ .PC′ —→⟨ L→M ⟩ M↠N) =
  _ ∣ μ ∣ PC —→⟨ prot-ctx L→M ⟩ prot-ctx-mult vc′ M↠N

prot!-ctx-mult : ∀ {M N μ μ′ PC PC′} {A ℓ}
  → (vc′ : LVal PC′)
  → M ∣ μ ∣ PC′ —↠ N ∣ μ′
  → prot! PC′ vc′ ℓ M A ∣ μ ∣ PC —↠ prot! PC′ vc′ ℓ N A ∣ μ′
prot!-ctx-mult vc′ (_ ∣ _ ∣ _ ∎) = _ ∣ _ ∣ _ ∎
prot!-ctx-mult {PC = PC} {PC′} vc′ (L ∣ μ ∣ .PC′ —→⟨ L→M ⟩ M↠N) =
  _ ∣ μ ∣ PC —→⟨ prot!-ctx L→M ⟩ prot!-ctx-mult vc′ M↠N


-- pres-mult : ∀ {Σ gc pc M M′ A μ μ′}
--   → [] ; Σ ; gc ; pc ⊢ M ⦂ A
--   → Σ ⊢ μ
--   → M ∣ μ ∣ pc —↠ M′ ∣ μ′
--     ---------------------------------------------------------------
--   → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; pc ⊢ M′ ⦂ A) × (Σ′ ⊢ μ′)
-- pres-mult {Σ} ⊢M ⊢μ pc≲gc (_ ∣ _ ∣ _ ∎) =
--   ⟨ Σ , ⊇-refl Σ , ⊢M , ⊢μ ⟩
-- pres-mult ⊢M ⊢μ pc≲gc (M ∣ μ ∣ pc —→⟨ M→N ⟩ N↠M′) =
--   let ⟨ Σ′ , Σ′⊇Σ , ⊢N , ⊢μ′ ⟩ = preserve ⊢M ⊢μ pc≲gc M→N in
--   let ⟨ Σ″ , Σ″⊇Σ′ , ⊢M′ , ⊢μ″ ⟩ = pres-mult ⊢N ⊢μ′ pc≲gc N↠M′ in
--   ⟨ Σ″ , ⊇-trans Σ″⊇Σ′ Σ′⊇Σ , ⊢M′ , ⊢μ″ ⟩


cast-reduction-inv : ∀ {A B M V W μ PC} {c : Cast A ⇒ B}
  → Value V
  → M ∣ μ ∣ PC —↠ W ∣ μ
  → M ≡ V ⟨ c ⟩
    --------------------------------
  → V ⟨ c ⟩ —↠ W
cast-reduction-inv v (_ ∣ _ ∣ _ ∎) refl = _ ∎
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ ξ {F = □⟨ c ⟩} r ⟩ r*) refl =
  contradiction r (Value⌿→ v)
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ ξ-blame {F = □⟨ c ⟩} ⟩ r*) refl =
  case v of λ where (V-raw ())
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ cast v† (cast vᵣ r+ 𝓋) ⟩ r*) refl =
  _ —→⟨ cast vᵣ r+ 𝓋 ⟩ (cast-reduction-inv (V-raw vᵣ) r* refl)
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ cast v† (cast-blame vᵣ c̅↠⊥) ⟩ _ ∣ _ ∣ _ ∎) refl =
  _ —→⟨ cast-blame vᵣ c̅↠⊥ ⟩ _ ∎
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ cast v† (cast-blame vᵣ c̅↠⊥) ⟩ _ ∣ _ ∣ _ —→⟨ r ⟩ r*) refl =
  contradiction r (Result⌿→ fail)
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ cast v† cast-id ⟩ $ _ ∣ _ ∣ _ ∎) refl =
  _ —→⟨ cast-id ⟩ _ ∎
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ cast v† cast-id ⟩ $ _ ∣ _ ∣ _ —→⟨ r ⟩ r*) refl =
  contradiction r (Value⌿→ v)
cast-reduction-inv v (_ ∣ _ ∣ _ —→⟨ cast v† (cast-comp vᵣ i) ⟩ r*) refl =
  _ —→⟨ cast-comp vᵣ i ⟩ (cast-reduction-inv (V-raw vᵣ) r* refl)
