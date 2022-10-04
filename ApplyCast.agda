{- DEPRECATED!! -}


module ApplyCast where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import CCSyntax Cast_⇒_
open import CCTyping Cast_⇒_
open import Values


apply-cast : ∀ {Γ Σ gc pc A B}
  → (V : Term) → Γ ; Σ ; gc ; pc ⊢ V ⦂ A → Value V
  → (c : Cast A ⇒ B) → Active c → Term
-- V ⟨ ` ι of g ⇒ ` ι of g ⟩ —→ V
apply-cast V ⊢V v c (A-base-id .c) = V
apply-cast V ⊢V v c (A-base-proj (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty ⋆~ ~-ι))) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , cast (` ι of l ℓ′) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
      W , refl , I-base-inj _ , _ , <:-ty <:-⋆ <:-ι ⟩ →
      case ℓ′ ≼? ℓ of λ where
        (yes _) → W
        (no  _) → error (blame p)
{- Order of reduction: propagate label first and then the security effect
        V ⟨ [ pc′ ] A₁ → A₂ of ℓ′ ⇒ [ ⋆ ] B₁ → B₂ of ⋆ ⟩ ⟨ [ ⋆ ] C₁ → C₂ of ⋆ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩
   —→ V ⟨ [ pc′ ] A₁ → A₂ of ℓ  ⇒ [ ⋆ ] B₁ → B₂ of ℓ ⟩ ⟨ [ ⋆ ] C₁ → C₂ of ℓ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩   , if ℓ′ ≼ ℓ
   —→ V ⟨ [ pc  ] A₁ → A₂ of ℓ  ⇒ [ pc ] B₁ → B₂ of ℓ ⟩ ⟨ [ pc ] C₁ → C₂ of ℓ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩ , if pc ≼ pc′
   -}
apply-cast V ⊢V v c (A-fun (cast ([ gc₁ ] C₁ ⇒ C₂ of ⋆) ([ gc₂ ] D₁ ⇒ D₂ of g) p (~-ty _ C~D)) a) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty _ A~B) ,
      W , refl , I-fun _ I-label I-label , _ , <:-ty <:-⋆ _ ⟩ →
      case a of λ where
        --      W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ′ ⇒ [ gc₂′ ] B₁ → B₂ of ⋆  ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ⋆  ⇒ [ gc₂ ] D₁ → D₂ of ⋆ ⟩
        -- —→ W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ′ ⇒ [ gc₂′ ] B₁ → B₂ of ℓ′ ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ℓ′ ⇒ [ gc₂ ] D₁ → D₂ of ⋆ ⟩
        A-id⋆ →
          let c~₁ = ~-ty ~ₗ-refl A~B
              c~₂ = ~-ty ~⋆      C~D in
            W ⟨ cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of l ℓ′) q c~₁ ⟩
              ⟨ cast ([ gc₁  ] C₁ ⇒ C₂ of l ℓ′) ([ gc₂  ] D₁ ⇒ D₂ of ⋆   ) p c~₂ ⟩
        --      W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ′ ⇒ [ gc₂′ ] B₁ → B₂ of ⋆ ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ⋆ ⇒ [ gc₂ ] D₁ → D₂ of ℓ ⟩
        -- —→ W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ  ⇒ [ gc₂′ ] B₁ → B₂ of ℓ ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ℓ ⇒ [ gc₂ ] D₁ → D₂ of ℓ ⟩  , if ℓ′ ≼ ℓ
        --      blame p  , otherwise
        (A-proj {ℓ}) →
          case ℓ′ ≼? ℓ of λ where
            (yes _) →
              let c~₁ = ~-ty ~ₗ-refl A~B
                  c~₂ = ~-ty ~ₗ-refl C~D in
                W ⟨ cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ) ([ gc₂′ ] B₁ ⇒ B₂ of l ℓ) q c~₁ ⟩
                  ⟨ cast ([ gc₁  ] C₁ ⇒ C₂ of l ℓ) ([ gc₂  ] D₁ ⇒ D₂ of l ℓ) p c~₂ ⟩
            (no _) → error (blame p)
apply-cast V ⊢V v c (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of g₁) ([ gc ] D₁ ⇒ D₂ of g₂) p (~-ty g₁~g₂ (~-fun _ C₁~D₁ C₂~D₂))) a I-label) =
  case canonical-pc⋆ ⊢V v of λ where
    ⟨ _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun _ A₁~B₁ A₂~B₂)) ,
      W , refl , I-fun _ I-label I-label , _ , <:-ty _ (<:-fun <:-⋆ _ _) ⟩ →
      case a of λ where
        --      W ⟨ [ pc′ ] A₁ → A₂ of g₁′ ⇒ [ ⋆   ] B₁ → B₂ of g₂′ ⟩ ⟨ [ ⋆   ] C₁ → C₂ of g₁ ⇒ [ ⋆ ] D₁ → D₂ of g₂ ⟩
        -- —→ W ⟨ [ pc′ ] A₁ → A₂ of g₁′ ⇒ [ pc′ ] B₁ → B₂ of g₂′ ⟩ ⟨ [ pc′ ] C₁ → C₂ of g₁ ⇒ [ ⋆ ] D₁ → D₂ of g₂ ⟩
        A-id⋆ →
          let c~₁ = ~-ty g₁′~g₂′ (~-fun ~ₗ-refl A₁~B₁ A₂~B₂)
              c~₂ = ~-ty g₁~g₂   (~-fun ~⋆ C₁~D₁ C₂~D₂) in
            W ⟨ cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ l pc′ ] B₁ ⇒ B₂ of g₂′) q c~₁ ⟩
              ⟨ cast ([ l pc′ ] C₁ ⇒ C₂ of g₁)  ([ ⋆ ] D₁ ⇒ D₂ of g₂) p c~₂ ⟩
        --      W ⟨ [ pc′ ] A₁ → A₂ of g₁′ ⇒ [ ⋆  ] B₁ → B₂ of g₂′ ⟩ ⟨ [ ⋆  ] C₁ → C₂ of g₁ ⇒ [ pc ] D₁ → D₂ of g₂ ⟩
        -- —→ W ⟨ [ pc  ] A₁ → A₂ of g₁′ ⇒ [ pc ] B₁ → B₂ of g₂′ ⟩ ⟨ [ pc ] C₁ → C₂ of g₁ ⇒ [ pc ] D₁ → D₂ of g₂ ⟩  , if pc ≼ pc′
        --      blame p  , otherwise
        (A-proj {pc}) →
          case pc ≼? pc′ of λ where
            (yes _) →
              let c~₁ = ~-ty g₁′~g₂′ (~-fun ~ₗ-refl A₁~B₁ A₂~B₂)
                  c~₂ = ~-ty g₁~g₂   (~-fun ~ₗ-refl C₁~D₁ C₂~D₂) in
              W ⟨ cast ([ l pc ] A₁ ⇒ A₂ of g₁′) ([ l pc ] B₁ ⇒ B₂ of g₂′) q c~₁ ⟩
                ⟨ cast ([ l pc ] C₁ ⇒ C₂ of g₁ ) ([ l pc ] D₁ ⇒ D₂ of g₂ ) p c~₂ ⟩
            (no _) → error (blame p)
apply-cast V ⊢V v c (A-ref (cast (Ref C of ⋆) (Ref D of g) p (~-ty _ RefC~RefD)) a) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
      W , refl , I-ref _ I-label I-label , _ , <:-ty <:-⋆ _ ⟩ →
      case a of λ where
        --      W ⟨ Ref A of ℓ′ ⇒ Ref B of ⋆  ⟩ ⟨ Ref C of ⋆  ⇒ Ref D of ⋆ ⟩
        -- —→ W ⟨ Ref A of ℓ′ ⇒ Ref B of ℓ′ ⟩ ⟨ Ref C of ℓ′ ⇒ Ref D of ⋆ ⟩
        A-id⋆ →
          let c~₁ = ~-ty ~ₗ-refl RefA~RefB
              c~₂ = ~-ty ~⋆      RefC~RefD in
            W ⟨ cast (Ref A of l ℓ′) (Ref B of l ℓ′) q c~₁ ⟩ ⟨ cast (Ref C of l ℓ′) (Ref D of ⋆) p c~₂ ⟩
        --      W ⟨ Ref A of ℓ′ ⇒ Ref B of ⋆ ⟩ ⟨ Ref C of ⋆ ⇒ Ref D of ℓ ⟩
        -- —→ W ⟨ Ref A of ℓ  ⇒ Ref B of ℓ ⟩ ⟨ Ref C of ℓ ⇒ Ref D of ℓ ⟩  , if ℓ′ ≼ ℓ
        --      blame p                                                       , otherwise
        (A-proj {ℓ}) →
          case ℓ′ ≼? ℓ of λ where
            (yes _) →
              let c~₁ = ~-ty ~ₗ-refl RefA~RefB
                  c~₂ = ~-ty ~ₗ-refl RefC~RefD in
                W ⟨ cast (Ref A of l ℓ) (Ref B of l ℓ) q c~₁ ⟩ ⟨ cast (Ref C of l ℓ) (Ref D of l ℓ) p c~₂ ⟩
            (no _) → error (blame p)
apply-cast V ⊢V v c (A-ref-ref (cast (Ref (S of ⋆) of g₁) (Ref (T of g₂₁) of g₂) p (~-ty g₁~g₂ (~-ref (~-ty _ S~T)))) a I-label) =
  case canonical-ref⋆ ⊢V v of λ where
    ⟨ _ , _ , cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of ⋆) of g₂′) q (~-ty g₁′~g₂′ (~-ref (~-ty _ S′~T′))) ,
      W , refl , I-ref _ I-label I-label , _ , <:-ty _ (<:-ref (<:-ty <:-⋆ _) (<:-ty <:-⋆ _)) ⟩ →
      case a of λ where
        --      W ⟨ Ref (S′ of ℓ₁′) of g₁′ ⇒ Ref (T′ of  ⋆ ) of g₂′ ⟩ ⟨ Ref (S of  ⋆ ) of g₁ ⇒ Ref (T of ⋆) of g₂ ⟩
        -- —→ W ⟨ Ref (S′ of ℓ₁′) of g₁′ ⇒ Ref (T′ of ℓ₁′) of g₂′ ⟩ ⟨ Ref (S of ℓ₁′) of g₁ ⇒ Ref (T of ⋆) of g₂ ⟩
        A-id⋆ →
          let c~₁ = ~-ty g₁′~g₂′ (~-ref (~-ty ~ₗ-refl S′~T′))
              c~₂ = ~-ty g₁~g₂   (~-ref (~-ty ~⋆ S~T)) in
          W ⟨ cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of l ℓ₁′) of g₂′) q c~₁ ⟩
            ⟨ cast (Ref (S of l ℓ₁′) of g₁)   (Ref (T of ⋆) of g₂) p c~₂ ⟩
        --      W ⟨ Ref (S′ of ℓ₁′) of g₁′ ⇒ Ref (T′ of  ⋆ ) of g₂′ ⟩ ⟨ Ref (S of  ⋆ ) of g₁ ⇒ Ref (T of ℓ₁) of g₂ ⟩
        -- —→ W ⟨ Ref (S′ of ℓ₁ ) of g₁′ ⇒ Ref (T′ of  ℓ₁) of g₂′ ⟩ ⟨ Ref (S of  ℓ₁) of g₁ ⇒ Ref (T of ℓ₁) of g₂ ⟩ , if ℓ₁′ = ℓ₁
        --      blame p  , otherwise
        (A-proj {ℓ₁}) →
          case ℓ₁′ =? ℓ₁ of λ where
            (yes _) →
              let c~₁ = ~-ty g₁′~g₂′ (~-ref (~-ty ~ₗ-refl S′~T′))
                  c~₂ = ~-ty g₁~g₂   (~-ref (~-ty ~ₗ-refl S~T)) in
              W ⟨ cast (Ref (S′ of l ℓ₁) of g₁′) (Ref (T′ of l ℓ₁) of g₂′) q c~₁ ⟩
                ⟨ cast (Ref (S of l ℓ₁) of g₁)   (Ref (T of l ℓ₁) of g₂) p c~₂ ⟩
            (no _) → error (blame p)
