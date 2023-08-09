module CC2.Sim where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; subst₂; sym)
open import Function using (case_of_)

open import Syntax
open import Common.Utils
open import Memory.HeapContext
open import CoercionExpr.Precision using (coerce⇒⋆-prec)
open import CoercionExpr.SyntacComp
open import LabelExpr.CatchUp renaming (catchup to catchupₑ)
open import LabelExpr.Security
open import LabelExpr.NSU
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision
open import CC2.CatchUp
open import CC2.SimCast
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value


sim : ∀ {Σ₁ Σ₁′ gc gc′} {M M′ N′ μ₁ μ₁′ μ₂′ PC PC′} {A A′}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ₁ ; Σ₁′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
  → Σ₁ ⊑ₘ Σ₁′
  → Σ₁ ; Σ₁′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → M′ ∣ μ₁′ ∣ PC′ —→ N′ ∣ μ₂′
    ------------------------------------------------------
  → ∃[ Σ₂ ] ∃[ Σ₂′ ] ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′) ×
       (Σ₂ ; Σ₂′ ⊢ μ₂ ⊑ μ₂′)
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ξ M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ ξ-blame = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot-val v) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ prot-blame = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot!-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (prot!-val v) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ prot!-blame = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (cast x x₁) = {!!}

{- β -}
sim vc vc′ _ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β vM′ vc′†) = {!!}
-- sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
--     (⊑-app {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β vM′ vc′†)
--   rewrite uniq-LVal vc′† vc′
--   with catchup {μ = μ} {PC} (V-raw V-ƛ) L⊑L′
-- ... | ⟨ V , V-raw V-ƛ , L↠V , ⊑-lam g⊑g′ A⊑A′ N⊑N′ ⟩ =
--   case catchup {μ = μ} {PC} vM′ M⊑M′ of λ where
--   ⟨ W , w , M↠W , W⊑M′ ⟩ →
--     let ♣ = trans-mult (plug-cong (app□ M _ _ _) L↠V)
--               (trans-mult (plug-cong (app _ □ (V-raw V-ƛ) _ _ _) M↠W)
--               (_ ∣ _ ∣ _ —→⟨ β w vc ⟩ _ ∣ _ ∣ _ ∎)) in
--     ⟨ Σ , Σ′ , _ , μ , ♣ ,
--       ⊑-prot (substitution-pres-⊑ ? Σ⊑Σ′ N⊑N′ (value-⊑-pc W⊑M′ w vM′)) (stampₑ-pres-prec vc vc′ PC⊑PC′) (≡→≼ (stampₑ-security vc)) (≡→≼ (stampₑ-security vc′)) eq eq′ , μ⊑μ′ ⟩
-- ... | ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ ⟩ , V-cast V-ƛ (ir-fun 𝓋) ,
--         L↠V , ⊑-castl (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun {gc₁ = gc₁} d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) ⟩
--   with catchup {μ = μ} {PC} vM′ M⊑M′
-- ...   | ⟨ W , w , M↠W , W⊑M′ ⟩
--   with catchup {μ = μ} {PC} vM′ (⊑-castl W⊑M′ c⊑A′)
-- ...   | ⟨ W₁ , w₁ , W⟨c⟩↠W₁ , W₁⊑M′ ⟩ =
--   let ⟨ PC₁ , vc₁ , ↠PC₁ , PC₁⊑stampPC′ ⟩ = catchupₑ (stampₑ-LVal vc′) prec in
--   let ♣ = trans-mult (plug-cong (app□ M _ _ _) L↠V)
--               (trans-mult (plug-cong (app _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _ _) M↠W)
--               (_ ∣ _ ∣ _ —→⟨ app-cast w vc 𝓋 ↠PC₁ vc₁ (cast-reduction-inv w W⟨c⟩↠W₁ refl) w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
--   ⟨ Σ , Σ′ , _ , μ , ♣ ,
--     ⊑-prot (⊑-castl (substitution-pres-⊑ ? Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑M′ w₁ vM′)) d⊑B′) PC₁⊑stampPC′ (stamp-cast-security vc ⊢PC ↠PC₁ vc₁) (≡→≼ (stampₑ-security vc′)) eq eq′ , μ⊑μ′ ⟩
--   where
--   ⊢W = proj₁ (cc-prec-inv ? Σ⊑Σ′ W⊑M′)
--   ⊢PC = proj₁ (prec→⊢ PC⊑PC′)
--   prec : (stampₑ PC vc ℓ ⟪ d̅ ⟫) ⊑ stampₑ PC′ vc′ ℓ
--                    ⇐ gc₁ ⊑ (gc′ ⋎̃ (l ℓ))
--   prec = ⊑-castl (stampₑ-pres-prec vc vc′ PC⊑PC′) d̅⊑gc′

-- sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
--     (⊑-app!l {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq eq′)
--     Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β vM′ vc′†)
--   rewrite uniq-LVal vc′† vc′
--   with catchup {μ = μ} {PC} (V-raw V-ƛ) L⊑L′
-- ... | ⟨ V , V-raw V-ƛ , L↠V , () ⟩
-- ... | ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ ⟩ , V-cast V-ƛ (ir-fun 𝓋) ,
--         L↠V , ⊑-castl (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun {gc₁ = gc₁} {.⋆} d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) ⟩
--   with catchup {μ = μ} {PC} vM′ M⊑M′
-- ...   | ⟨ W , w , M↠W , W⊑M′ ⟩
--   with catchup {μ = μ} {PC} vM′ (⊑-castl W⊑M′ c⊑A′)
-- ...   | ⟨ W₁ , w₁ , W⟨c⟩↠W₁ , W₁⊑M′ ⟩ =
--   let ⟨ PC₁ , vc₁ , ↠PC₁ , PC₁⊑stampPC′ ⟩ = catchupₑ (stampₑ-LVal vc′) prec in
--   let ♣ = trans-mult (plug-cong (app!□ M _ _) L↠V)
--               (trans-mult (plug-cong (app! _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _) M↠W)
--               (_ ∣ _ ∣ _ —→⟨ app!-cast w vc 𝓋 ⊢PC ↠PC₁ vc₁ (cast-reduction-inv w W⟨c⟩↠W₁ refl) w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
--   ⟨ Σ , Σ′ , _ , μ , ♣ ,
--     ⊑-prot!l (⊑-castl (substitution-pres-⊑ ? Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑M′ w₁ vM′)) d⊑B′)
--              PC₁⊑stampPC′
--              (stamp⇒⋆-cast-security vc ⊢PC ↠PC₁ vc₁) (≡→≼ (stampₑ-security vc′)) eq eq′ (≡→≼ ∥c̅∥≡ℓ) , μ⊑μ′ ⟩
--   where
--   ∥PC∥⋎∥c̅∥≡∥stamp∥ = stampₑ-security {ℓ = ∥ c̅ ∥ₗ 𝓋} vc
--   ∥c̅∥≡ℓ = security-prec-left _ 𝓋 c̅⊑g′
--   ⊢PC = proj₁ (prec→⊢ PC⊑PC′)
--   ⊢W = proj₁ (cc-prec-inv ? Σ⊑Σ′ W⊑M′)
--   gc⊑ℓc : gc ⊑ₗ l ℓc
--   gc⊑ℓc = prec→⊑ PC⊑PC′
--   gc⋎ℓ⊑ℓc⋎ℓ : (gc ⋎̃ l ℓ) ⊑ₗ (l (ℓc ⋎ ℓ))
--   gc⋎ℓ⊑ℓc⋎ℓ = consis-join-⊑ₗ gc⊑ℓc l⊑l
--   prec : (stampₑ PC vc (∥ c̅ ∥ₗ 𝓋) ⟪ coerce gc ⋎̃ l (∥ c̅ ∥ₗ 𝓋) ⇒⋆ ⟫ ⟪ d̅ ⟫) ⊑ stampₑ PC′ vc′ ℓ
--                    ⇐ gc₁ ⊑ (gc′ ⋎̃ (l ℓ))
--   prec rewrite ∥c̅∥≡ℓ =
--       ⊑-castl (⊑-castl (stampₑ-pres-prec vc vc′ PC⊑PC′) (coerce⇒⋆-prec gc⋎ℓ⊑ℓc⋎ℓ)) d̅⊑gc′

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app-cast v vc′† 𝓋 x vc″ x₁ x₂) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app-blame-pc v vc′† 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app-blame v vc′† 𝓋 x vc″ x₁) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app!-cast v vc′† 𝓋 x x₁ vc″ x₂ x₃) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app!-blame-pc v vc′† 𝓋 x x₁) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (app!-blame v vc′† 𝓋 x x₁ vc″ x₂) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-if-true vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-if-false vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if-true-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if-false-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if!-true-cast vc′† 𝓋 x vc″) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (if!-false-cast vc′† 𝓋 x vc″) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-let x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ref v x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ref? v x x₁ x₂) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (ref?-blame-pc v x) = {!!}

sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-deref M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (deref {v = v′} μ′a≡V′)
  with catchup {μ = μ} {PC} (V-raw V-addr) M⊑M′
... | ⟨ addr _ , V-raw V-addr , L↠V , ⊑-addr a b ⟩ =
  let ⟨ V , v , μa≡V , V⊑V′ ⟩ = ⊑μ-lookup {w = v′} μ⊑μ′ μ′a≡V′ a b in
  ⟨ Σ , Σ′ , _ , μ ,
    trans-mult (plug-cong (!□ _ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref {v = v} μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
    ⊑-prot (value-⊑-pc V⊑V′ v v′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ ,
    μ⊑μ′ ⟩
... | ⟨ addr _ ⟨ cast (ref c d) c̅ ⟩ , V-cast V-addr (ir-ref 𝓋) ,
        L↠V , ⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩ =
  let ⟨ V , v , μa≡V , V⊑V′ ⟩ = ⊑μ-lookup {w = v′} {ℓ = ℓ} {n} μ⊑μ′ μ′a≡V′ a b in
  ⟨ Σ , Σ′ , _ , μ ,
    trans-mult (plug-cong (!□ _ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref-cast {v = v} 𝓋 μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
    ⊑-prot (⊑-castl (value-⊑-pc V⊑V′ v v′) d⊑A′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ ,
    μ⊑μ′ ⟩
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-deref!l M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (deref μ′a≡V′) =
  ⟨ Σ , Σ′ , {!_!} , μ , _ ∣ _ ∣ _ —→⟨ {!deref!} ⟩ {!!}  , {!!} , μ⊑μ′ ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (deref-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (deref!-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (β-assign v) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign-cast v 𝓋 x w) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign-blame v 𝓋 x) = {!!}

sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-assign? L⊑L′ M⊑V′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign?-cast v′ vc′† 𝓋′ ⊢PC′ ↠PC′₁ vc′₁ ↠W′ w′) = {!!}
--   rewrite uniq-LVal vc′† vc′
--   with catchup {μ = μ} {PC} (V-cast V-addr (ir-ref 𝓋′)) L⊑L′
-- ... | ⟨ V , v , L↠V , prec1 ⟩
--   with catchup {μ = μ} {PC} v′ M⊑V′
-- ... | ⟨ W , w , M↠W , prec2 ⟩
--   with v | prec1
-- ... | V-cast V-addr (ir-ref 𝓋) | ⊑-cast (⊑-addr a b) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) =
--   let ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′
--       ⊢PC = proj₁ (prec→⊢ PC⊑PC′) in
--   let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
--   let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
--   let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
--         (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
--          (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ⊢PC ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
--   ⟨ Σ , Σ′ , _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const , ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ ⟩
-- ... | V-cast V-addr (ir-ref 𝓋) | ⊑-castl (⊑-castr (⊑-addr a b) (⊑-ref A⊑c′ A⊑d′ ℓ⊑c̅′)) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
--   let c̅⊑c̅′ = comp-pres-⊑-rl ℓ⊑c̅′ c̅⊑g′
--       ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′
--       ⊢PC = proj₁ (prec→⊢ PC⊑PC′) in
--   let c⊑c′ = comp-pres-prec-lr c⊑A′ A⊑c′ in
--   let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
--   let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
--   let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
--         (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
--          (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ⊢PC ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
--   ⟨ Σ , Σ′ , _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const , ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ ⟩
-- ... | V-cast V-addr (ir-ref 𝓋) | ⊑-castr (⊑-castl (⊑-addr a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑ℓ)) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) =
--   let c̅⊑c̅′ = comp-pres-⊑-lr c̅⊑ℓ g⊑c̅′
--       ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′
--       ⊢PC = proj₁ (prec→⊢ PC⊑PC′) in
--   let c⊑c′ = comp-pres-prec-rl A⊑c′ c⊑A′ in
--   let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
--   let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
--   let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
--         (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
--          (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ⊢PC ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
--   ⟨ Σ , Σ′ , _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const , ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ ⟩
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign?-cast-blame-pc v vc′† 𝓋 x x₁) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ (assign?-cast-blame v vc′† 𝓋 x x₁ x₂ x₃) = {!!}
sim vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ M′→N′
  with sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ M′→N′
... | ⟨ Σ₂ , Σ₂′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ ⟩ =
  ⟨ Σ₂ , Σ₂′ , N ⟨ c ⟩ , μ₂ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ₂⊑μ₂′ ⟩
