module CoercionExpr.GG where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.SecurityLabels
open import Common.BlameLabels
open import CoercionExpr.CoercionExpr
open import CoercionExpr.Precision

open import CoercionExpr.CatchUp     using (catchup) public
open import CoercionExpr.Simulation  using (sim) public
open import CoercionExpr.CatchUpBack using (catchup-back) public
open import CoercionExpr.SimBack     using (sim-back) public


sim-mult : ∀ {g₁ g₁′ g₂ g₂′} {c̅₁ : CExpr g₁ ⇒ g₂} {c̅₁′ c̅₂′ : CExpr g₁′ ⇒ g₂′}
  → ⊢ c̅₁ ⊑ c̅₁′
  → CVal c̅₂′
  → c̅₁′ —↠ c̅₂′
    ---------------------------------------------------
  → ∃[ c̅₂ ] (CVal c̅₂) × (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ c̅₂′)
sim-mult c̅₁⊑c̅₁′ 𝓋′ (_ ∎) = catchup _ _ 𝓋′ c̅₁⊑c̅₁′
sim-mult {c̅₁ = c̅₁} c̅₁⊑c̅₁′ 𝓋′ (_ —→⟨ c̅₁′→c̅′ ⟩ c̅′↠c̅₂′) =
  let ⟨ c̅₂ ,     c̅₁↠c̅₂ , c̅₂⊑c̅′ ⟩  = sim c̅₁⊑c̅₁′ c̅₁′→c̅′ in
  let ⟨ c̅₃ , 𝓋 , c̅₂↠c̅₃ , c̅₃⊑c̅₂′ ⟩ = sim-mult c̅₂⊑c̅′ 𝓋′ c̅′↠c̅₂′ in
  ⟨ c̅₃ , 𝓋 , ↠-trans c̅₁↠c̅₂ c̅₂↠c̅₃ , c̅₃⊑c̅₂′ ⟩
