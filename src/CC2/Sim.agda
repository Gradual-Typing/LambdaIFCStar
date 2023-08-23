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
open import LabelExpr.Stamping
open import LabelExpr.NSU
open import CC2.Statics
open import CC2.Reduction
open import CC2.MultiStep
open import CC2.Precision
open import CC2.HeapPrecision
open import CC2.CatchUp
open import CC2.SimCast
open import CC2.SubstPrecision using (substitution-pres-⊑)
open import Memory.Heap Term Value hiding (Addr; a⟦_⟧_)


sim : ∀ {Σ₁ Σ₁′ gc gc′} {M M′ N′ μ₁ μ₁′ μ₂′ PC PC′} {A A′}
  → (vc  : LVal PC)
  → (vc′ : LVal PC′)
  → let ℓv  = ∥ PC  ∥ vc  in
     let ℓv′ = ∥ PC′ ∥ vc′ in
     [] ; [] ∣ Σ₁ ; Σ₁′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ M ⊑ M′ ⇐ A ⊑ A′
  → Σ₁ ⊑ₘ Σ₁′
  → Σ₁ ; Σ₁′ ⊢ μ₁ ⊑ μ₁′
  → PC ⊑ PC′ ⇐ gc ⊑ gc′
  → SizeEq μ₁ μ₁′
  → M′ ∣ μ₁′ ∣ PC′ —→ N′ ∣ μ₂′
    ------------------------------------------------------
  → ∃[ Σ₂ ] ∃[ Σ₂′ ] ∃[ N ] ∃[ μ₂ ]
       (M ∣ μ₁ ∣ PC —↠ N ∣ μ₂) ×
       ([] ; [] ∣ Σ₂ ; Σ₂′ ∣ gc ; gc′ ∣ ℓv ; ℓv′ ⊢ N ⊑ N′ ⇐ A ⊑ A′) ×
       (Σ₂ ; Σ₂′ ⊢ μ₂ ⊑ μ₂′) ×
       (SizeEq μ₂ μ₂′)
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ξ M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq ξ-blame = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot-val v) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq prot-blame = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot!-ctx M′→N′) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (prot!-val v) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq prot!-blame = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (cast x x₁) = {!!}

{- β -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-app {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β vM′ vc′†)
  rewrite uniq-LVal vc′† vc′
  with catchup {μ = μ} {PC} (V-raw V-ƛ) L⊑L′
... | ⟨ V , V-raw V-ƛ , L↠V , ⊑-lam g⊑g′ A⊑A′ N⊑N′ ⟩ =
  case catchup {μ = μ} {PC} vM′ M⊑M′ of λ where
  ⟨ W , w , M↠W , W⊑M′ ⟩ →
    let ♣ = trans-mult (plug-cong (app□ M _ _ _) L↠V)
              (trans-mult (plug-cong (app _ □ (V-raw V-ƛ) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ β w vc ⟩ _ ∣ _ ∣ _ ∎)) in
    let N[W]⊑N′[M′] = substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W⊑M′ w vM′) in
    ⟨ Σ , Σ′ , _ , μ , ♣ ,
      ⊑-prot N[W]⊑N′[M′] (stampₑ-prec vc vc′ PC⊑PC′) (≡→≼ (stampₑ-security vc)) (≡→≼ (stampₑ-security vc′)) eq eq′ ,
      μ⊑μ′ , size-eq ⟩
... | ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ ⟩ , V-cast V-ƛ (ir-fun 𝓋) ,
        L↠V , ⊑-castl (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun {gc₁ = gc₁} d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) ⟩
  with catchup {μ = μ} {PC} vM′ M⊑M′
...   | ⟨ W , w , M↠W , W⊑M′ ⟩
  with catchup {μ = μ} {PC} vM′ (⊑-castl W⊑M′ c⊑A′)
...   | ⟨ W₁ , w₁ , W⟨c⟩↠W₁ , W₁⊑M′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ , PC₁⊑stampPC′ ⟩ = catchupₑ (stampₑ-LVal vc′) prec in
  let ♣ = trans-mult (plug-cong (app□ M _ _ _) L↠V)
              (trans-mult (plug-cong (app _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ app-cast w vc 𝓋 ↠PC₁ vc₁ (cast-reduction-inv w W⟨c⟩↠W₁ refl) w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  let N[W₁]⊑N′[M′] = substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑M′ w₁ vM′) in
  ⟨ Σ , Σ′ , _ , μ , ♣ ,
    ⊑-prot (⊑-castl N[W₁]⊑N′[M′] d⊑B′) PC₁⊑stampPC′ (stamp-cast-security vc ⊢PC ↠PC₁ vc₁) (≡→≼ (stampₑ-security vc′)) eq eq′ ,
    μ⊑μ′ , size-eq ⟩
  where
  ⊢W = proj₁ (cc-prec-inv ⊑*-∅ Σ⊑Σ′ W⊑M′)
  ⊢PC = proj₁ (prec→⊢ PC⊑PC′)
  prec : (stampₑ PC vc ℓ ⟪ d̅ ⟫) ⊑ stampₑ PC′ vc′ ℓ
                   ⇐ gc₁ ⊑ (gc′ ⋎̃ (l ℓ))
  prec = ⊑-castl (stampₑ-prec vc vc′ PC⊑PC′) d̅⊑gc′

sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-app!l {ℓc = ℓc} {L = L} {L′} {M} {M′} {ℓ = ℓ} L⊑L′ M⊑M′ eq eq′)
    Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β vM′ vc′†)
  rewrite uniq-LVal vc′† vc′
  with catchup {μ = μ} {PC} (V-raw V-ƛ) L⊑L′
... | ⟨ V , V-raw V-ƛ , L↠V , () ⟩
... | ⟨ ƛ N ⟨ cast (fun d̅ c d) c̅ ⟩ , V-cast V-ƛ (ir-fun 𝓋) ,
        L↠V , ⊑-castl (⊑-lam gc⊑gc′ A⊑A′ N⊑N′) (⊑-fun {gc₁ = gc₁} {.⋆} d̅⊑gc′ c⊑A′ d⊑B′ c̅⊑g′) ⟩
  with catchup {μ = μ} {PC} vM′ M⊑M′
...   | ⟨ W , w , M↠W , W⊑M′ ⟩
  with catchup {μ = μ} {PC} vM′ (⊑-castl W⊑M′ c⊑A′)
...   | ⟨ W₁ , w₁ , W⟨c⟩↠W₁ , W₁⊑M′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ , PC₁⊑stampPC′ ⟩ = catchupₑ (stampₑ-LVal vc′) prec in
  let ♣ = trans-mult (plug-cong (app!□ M _ _) L↠V)
              (trans-mult (plug-cong (app! _ □ (V-cast V-ƛ (ir-fun 𝓋)) _ _) M↠W)
              (_ ∣ _ ∣ _ —→⟨ app!-cast w vc 𝓋 ↠PC₁ vc₁ (cast-reduction-inv w W⟨c⟩↠W₁ refl) w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ Σ , Σ′ , _ , μ , ♣ ,
    ⊑-prot!l (⊑-castl (substitution-pres-⊑ ⊑*-∅ Σ⊑Σ′ N⊑N′ (value-⊑-pc W₁⊑M′ w₁ vM′)) d⊑B′)
             PC₁⊑stampPC′
             (stamp!-cast-security vc ⊢PC ↠PC₁ vc₁) (≡→≼ (stampₑ-security vc′)) eq eq′ (≡→≼ ∥c̅∥≡ℓ) , μ⊑μ′ , size-eq ⟩
  where
  ∥PC∥⋎∥c̅∥≡∥stamp∥ = stampₑ-security {ℓ = ∥ c̅ ∥ₗ 𝓋} vc
  ∥c̅∥≡ℓ = security-prec-left _ 𝓋 c̅⊑g′
  ⊢PC = proj₁ (prec→⊢ PC⊑PC′)
  ⊢W = proj₁ (cc-prec-inv ⊑*-∅ Σ⊑Σ′ W⊑M′)
  prec : (stamp!ₑ PC vc (∥ c̅ ∥ₗ 𝓋) ⟪ d̅ ⟫) ⊑ stampₑ PC′ vc′ ℓ
                   ⇐ gc₁ ⊑ (gc′ ⋎̃ (l ℓ))
  prec rewrite ∥c̅∥≡ℓ = ⊑-castl (stamp!ₑ-left-prec vc vc′ PC⊑PC′) d̅⊑gc′

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-cast v vc′† 𝓋 x vc″ x₁ x₂) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-blame-pc v vc′† 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app-blame v vc′† 𝓋 x vc″ x₁) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-cast v vc′† 𝓋 _ _ _ _) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-blame-pc v vc′† 𝓋 _) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (app!-blame v vc′† 𝓋 _ _ _) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-if-true vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-if-false vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if-true-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if-false-cast vc′†) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if!-true-cast vc′† 𝓋) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (if!-false-cast vc′† 𝓋) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-let x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref v x) = {!!}

{- ref? -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-ref? {T = T} {T′} {ℓ} M⊑V′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref? {n = n} v′ fresh′ ↠PC′₁ vc′₁)
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ V , v , M↠V , V⊑V′ ⟩ =
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-ref PC⊑PC′ vc vc′ ↠PC′₁ vc′₁ in
  let fresh = size-eq-fresh size-eq fresh′ in
  ⟨ cons-Σ (a⟦ ℓ ⟧ n) T Σ , cons-Σ (a⟦ ℓ ⟧ n) T′ Σ′ , _ , cons-μ (a⟦ ℓ ⟧ n) _ v μ ,
    trans-mult (plug-cong (ref?⟦ _ ⟧□ _) M↠V)
               (_ ∣ _ ∣ _ —→⟨ ref? v fresh ↠PC₁ vc₁ ⟩ _ ∣ _ ∣ _ ∎) ,
    ⊑-addr (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ) (lookup-Σ-cons (a⟦ ℓ ⟧ n) Σ′) ,
    ⊑μ-new Σ⊑Σ′ μ⊑μ′ (value-⊑-pc V⊑V′ v v′) v v′ fresh fresh′ ,
    size-eq-cons {v = v} {v′} {n} {ℓ} size-eq ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (ref?-blame-pc v x) = {!!}

{- deref -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-deref M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref {v = v′} μ′a≡V′)
  with catchup {μ = μ} {PC} (V-raw V-addr) M⊑M′
... | ⟨ addr _ , V-raw V-addr , L↠V , ⊑-addr {n = n} {ℓ̂ = ℓ} a b ⟩ =
  let ⟨ _ , _ , V , v , V′ , v′ , μa≡V , μ′a≡V†′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ a b in
  case trans (sym μ′a≡V′) μ′a≡V†′ of λ where
  refl → ⟨ Σ , Σ′ , _ , μ ,
    trans-mult (plug-cong (!□ _ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref {v = v} μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
    ⊑-prot (value-⊑-pc V⊑V′ v v′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ ,
    μ⊑μ′ , size-eq ⟩
... | ⟨ addr _ ⟨ cast (ref c d) c̅ ⟩ , V-cast V-addr (ir-ref 𝓋) ,
        L↠V , ⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩ =
  let ⟨ _ , _ , V , v , V′ , v′ , μa≡V , μ′a≡V†′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ a b in
  case trans (sym μ′a≡V′) μ′a≡V†′ of λ where
  refl → ⟨ Σ , Σ′ , _ , μ ,
    trans-mult (plug-cong (!□ _ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref-cast {v = v} 𝓋 μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
    ⊑-prot (⊑-castl (value-⊑-pc V⊑V′ v v′) d⊑A′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ ,
    μ⊑μ′ , size-eq ⟩
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-deref!l M⊑M′ eq eq′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref {v = v′} μ′a≡V′)
  with catchup {μ = μ} {PC} (V-raw V-addr) M⊑M′
... | ⟨ addr _ , V-raw V-addr , L↠V , () ⟩
... | ⟨ addr _ ⟨ cast (ref c d) c̅ ⟩ , V-cast V-addr (ir-ref 𝓋) ,
        L↠V , ⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) ⟩ =
  let ⟨ _ , _ , V , v , V′ , v′ , μa≡V , μ′a≡V†′ , V⊑V′ ⟩ = μ⊑μ′ n ℓ a b in
  case trans (sym μ′a≡V′) μ′a≡V†′ of λ where
  refl → ⟨ Σ , Σ′ , _ , μ ,
    trans-mult (plug-cong (!!□ _) L↠V) (_ ∣ _ ∣ _ —→⟨ deref!-cast {v = v} 𝓋 μa≡V ⟩ _ ∣ _ ∣ _ ∎ ) ,
    ⊑-prot!l (⊑-castl (value-⊑-pc V⊑V′ v v′) d⊑A′) ⊑-l (_ ≼high) (_ ≼high) eq eq′ (≡→≼ (security-prec-left _ 𝓋 c̅⊑g′)) ,
    μ⊑μ′ , size-eq ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (deref!-cast 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (β-assign v) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign-cast v 𝓋 x w) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign-blame v 𝓋 x) = {!!}

{- assign?-cast -}
sim {Σ} {Σ′} {gc} {gc′} {μ₁ = μ} {PC = PC} {PC′} vc vc′
    (⊑-assign? L⊑L′ M⊑V′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast v′ vc′† 𝓋′ ↠PC′₁ vc′₁ ↠W′ w′)
  rewrite uniq-LVal vc′† vc′
  with catchup {μ = μ} {PC} (V-cast V-addr (ir-ref 𝓋′)) L⊑L′
... | ⟨ V , v , L↠V , prec1 ⟩
  with catchup {μ = μ} {PC} v′ M⊑V′
... | ⟨ W , w , M↠W , prec2 ⟩
  with v | prec1
... | V-cast V-addr (ir-ref 𝓋)
    | ⊑-cast (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑c′ d⊑d′ c̅⊑c̅′) =
  let ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
  let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
        (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
         (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ Σ , Σ′ , _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
    size-eq-cons {v = w₁} {w′} {n} {ℓ} size-eq ⟩
... | V-cast V-addr (ir-ref 𝓋)
    | ⊑-castl (⊑-castr (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref A⊑c′ A⊑d′ ℓ⊑c̅′)) (⊑-ref c⊑A′ d⊑A′ c̅⊑g′) =
  let c̅⊑c̅′ = comp-pres-⊑-rl ℓ⊑c̅′ c̅⊑g′
      ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
  let c⊑c′ = comp-pres-prec-lr c⊑A′ A⊑c′ in
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
  let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
        (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
         (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ Σ , Σ′ , _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
    size-eq-cons {v = w₁} {w′} {n} {ℓ} size-eq ⟩
... | V-cast V-addr (ir-ref 𝓋)
    | ⊑-castr (⊑-castl (⊑-addr {n = n} {ℓ̂ = ℓ} a b) (⊑-ref c⊑A′ d⊑A′ c̅⊑ℓ)) (⊑-ref A⊑c′ A⊑d′ g⊑c̅′) =
  let c̅⊑c̅′ = comp-pres-⊑-lr c̅⊑ℓ g⊑c̅′
      ℓ≼ℓ′ = security-prec _ _ 𝓋 𝓋′ c̅⊑c̅′ in
  let c⊑c′ = comp-pres-prec-rl A⊑c′ c⊑A′ in
  let ⟨ PC₁ , vc₁ , ↠PC₁ ⟩ = sim-nsu-assign PC⊑PC′ vc vc′ ℓ≼ℓ′ ↠PC′₁ vc′₁ in
  let ⟨ W₁ , w₁ , ↠W₁ , W₁⊑W′ ⟩ = sim-cast prec2 w v′ c⊑c′ ↠W′ w′ in
  let ♣ = trans-mult (plug-cong (assign?□ _ _ _ _) L↠V)
        (trans-mult (plug-cong (assign? _ □ (V-cast V-addr (ir-ref 𝓋)) _ _ _) M↠W)
         (_ ∣ _ ∣ _ —→⟨ assign?-cast w vc 𝓋 ↠PC₁ vc₁ ↠W₁ w₁ ⟩ _ ∣ _ ∣ _ ∎)) in
  ⟨ Σ , Σ′ , _ , cons-μ _ W₁ w₁ _ , ♣ , ⊑-const ,
    ⊑μ-update μ⊑μ′ (value-⊑-pc W₁⊑W′ w₁ w′) w₁ w′ a b ,
    size-eq-cons {v = w₁} {w′} {n} {ℓ} size-eq ⟩

sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast-blame-pc v vc′† 𝓋 x) = {!!}
sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq (assign?-cast-blame v vc′† 𝓋 x x₁ x₂) = {!!}

sim vc vc′ (⊑-castl {c = c} M⊑M′ c⊑A′) Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′
  with sim vc vc′ M⊑M′ Σ⊑Σ′ μ⊑μ′ PC⊑PC′ size-eq M′→N′
... | ⟨ Σ₂ , Σ₂′ , N , μ₂ , M↠N , N⊑N′ , μ₂⊑μ₂′ , size-eq′ ⟩ =
  ⟨ Σ₂ , Σ₂′ , N ⟨ c ⟩ , μ₂ , plug-cong □⟨ c ⟩ M↠N , ⊑-castl N⊑N′ c⊑A′ , μ₂⊑μ₂′ , size-eq′ ⟩
