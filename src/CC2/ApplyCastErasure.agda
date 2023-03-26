module CC.ApplyCastErasure where

open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Common.Utils
open import Common.Types
open import CC.CCStatics
open import CC.ApplyCast
open import CC.Erasure


applycast-erase : ∀ {A B V N} {c : Cast A ⇒ B}
  → ApplyCast V , c ↝ N
  → ¬ Err N
    --------------------------
  → erase V ≡ erase N
applycast-erase cast-base-id _ = refl
applycast-erase (cast-base-proj _) _ = refl
applycast-erase cast-fun-id⋆ _ = refl
applycast-erase (cast-fun-proj _) _ = refl
applycast-erase cast-fun-pc-id⋆ _ = refl
applycast-erase (cast-fun-pc-proj _) _ = refl
applycast-erase cast-ref-id⋆ _ = refl
applycast-erase (cast-ref-proj _) _ = refl
applycast-erase cast-ref-ref-id⋆ _ = refl
applycast-erase (cast-ref-ref-proj _) _ = refl
applycast-erase (cast-base-proj-blame _) ¬errN = contradiction E-error ¬errN
applycast-erase (cast-fun-proj-blame _) ¬errN = contradiction E-error ¬errN
applycast-erase (cast-fun-pc-proj-blame _) ¬errN = contradiction E-error ¬errN
applycast-erase (cast-ref-proj-blame _) ¬errN = contradiction E-error ¬errN
applycast-erase (cast-ref-ref-proj-blame _) ¬errN = contradiction E-error ¬errN
