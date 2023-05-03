module LabelCoercionCalculi.CatchUp where

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
open import LabelCoercionCalculi.CoercionExp



{- Lemma: Catching up to value on the more precise side -}
catchup : ∀ {g₁ g₁′ g₂ g₂′} (c̅ : CoercionExp g₁ ⇒ g₂) (c̅′ : CoercionExp g₁′ ⇒ g₂′)
  → 𝒱 c̅′
  → ⊢ c̅ ⊑ c̅′
    -------------------------------------------------
  → ∃[ c̅ₙ ] (𝒱 c̅ₙ ) × (c̅ —↠ c̅ₙ) × (⊢ c̅ₙ ⊑ c̅′)


catchup-to-id : ∀ {g₁ g₂ g′}
  → (c̅₁ : CoercionExp g₁ ⇒ g₂)
  → ⊢ c̅₁ ⊑ id g′
  → ∃[ c̅₂ ] (𝒱 c̅₂) × (c̅₁ —↠ c̅₂) × (⊢ c̅₂ ⊑ id g′)
catchup-to-id (id _) (⊑-id g⊑g′) = ⟨ id _ , id , id _ ∎ , ⊑-id g⊑g′ ⟩
catchup-to-id (c̅ ⨾ ↑) (⊑-castl c̅⊑id low⊑g′ high⊑g′) =
  case ⟨ low⊑g′ , high⊑g′ ⟩ of λ where
  ⟨ l⊑l , () ⟩  {- g′ can't be high and low at the same time -}
catchup-to-id (c̅ ⨾ ℓ ?? p) (⊑-castl c̅⊑id ⋆⊑ (l⊑l {ℓ}))
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , id {⋆} , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ id ⋆ ⨾ ℓ ?? p , id⨾? , plug-cong c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ ℓ₀ ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id ⟩
catchup-to-id (c̅ ⨾ ℓ !) (⊑-castl c̅⊑id (l⊑l {ℓ}) ⋆⊑)
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ c̅ₙ ⨾ ℓ ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩
catchup-to-id (c̅ ⨾ id g) (⊑-castl c̅⊑id _ _)
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩  =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑id ⟩


catchup-to-inj : ∀ {g₁ g₂ g′ ℓ′}
  → (c̅   : CoercionExp g₁ ⇒ g₂  )
  → (c̅ₙ′ : CoercionExp g′ ⇒ l ℓ′)
  → 𝒱 c̅ₙ′
  → ⊢ c̅ ⊑ c̅ₙ′ ⨾ ℓ′ !
    -----------------------------------------------------
  → ∃[ c̅ₙ ] (𝒱 c̅ₙ) × (c̅ —↠ c̅ₙ) × (⊢ c̅ₙ ⊑ c̅ₙ′ ⨾ ℓ′ !)
catchup-to-inj (c̅ ⨾ ℓ !) c̅ₙ′ v′ (⊑-cast c̅⊑c̅ₙ′ (l⊑l {ℓ}) ⋆⊑)
  with catchup c̅ c̅ₙ′ v′ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ ⨾ ℓ ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑c̅ₙ′ l⊑l ⋆⊑ ⟩
catchup-to-inj (c̅ ⨾ id ⋆) c̅ₙ′ v′ (⊑-cast  c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-inj c̅ c̅ₙ′ v′ (⊑-castr c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′ ⟩
catchup-to-inj (c̅ ⨾ id ⋆) c̅ₙ′ v′ (⊑-castl c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-inj c̅ c̅ₙ′ v′ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′ ⟩
catchup-to-inj c̅ c̅ₙ′ v′ (⊑-castr c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup c̅ c̅ₙ′ v′ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ , v , c̅↠c̅ₙ , ⊑-castr c̅ₙ⊑c̅ₙ′ ⋆⊑ ⋆⊑ ⟩


catchup-to-id⨾? : ∀ {g₁ g₂ ℓ′} {p}
  → (c̅   : CoercionExp g₁ ⇒ g₂)
  → ⊢ c̅ ⊑ id ⋆ ⨾ ℓ′ ?? p
    --------------------------------------------------------
  → ∃[ c̅ₙ ] (𝒱 c̅ₙ) × (c̅ —↠ c̅ₙ) × (⊢ c̅ₙ ⊑ id ⋆ ⨾ ℓ′ ?? p)
catchup-to-id⨾? (c̅ ⨾ id ⋆) (⊑-cast c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-id c̅ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , ⊑-castr c̅ₙ⊑id ⋆⊑ ⋆⊑ ⟩
catchup-to-id⨾? (c̅ ⨾ ℓ ?? p) (⊑-cast c̅⊑c̅ₙ′ ⋆⊑ l⊑l)
  with catchup-to-id c̅ c̅⊑c̅ₙ′
... | ⟨ id ⋆ , id , c̅↠c̅ₙ , ⊑-id ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ ℓ ?? p , id⨾? , plug-cong c̅↠c̅ₙ , ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ ℓ₀ ! , inj v , c̅↠c̅ₙ , ⊑-castl _ () ⋆⊑ ⟩                                                 {- impossible -}
catchup-to-id⨾? (c̅ ⨾ c) (⊑-castl c̅⊑c̅ₙ′ g₃⊑ℓ′ g₂⊑ℓ′)
  with catchup-to-id⨾? c̅ c̅⊑c̅ₙ′ | g₃⊑ℓ′ | g₂⊑ℓ′ | c
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | ⋆⊑ | ⋆⊑ | id ⋆ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′ ⟩
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩ | l⊑l {ℓ′} | l⊑l {ℓ′} | id (l ℓ′) =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′ ⟩
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id⨾? ⟩ | l⊑l {ℓ′} | ⋆⊑ | ℓ′ ! =
  ⟨ c̅ₙ ⨾ ℓ′ ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id⨾? g₃⊑ℓ′ g₂⊑ℓ′ ⟩
... | ⟨ id ⋆ , id , c̅↠id , ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑ ⟩ | ⋆⊑ | l⊑l {ℓ′} | ℓ′ ?? p =
  ⟨ id ⋆ ⨾ ℓ′ ?? p , id⨾? , plug-cong c̅↠id , ⊑-cast (⊑-id ⋆⊑) ⋆⊑ g₂⊑ℓ′ ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id⨾? _ _ ⟩ | ⋆⊑ | l⊑l {low} | low ?? p =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾? ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castl _ () ⋆⊑) ⋆⊑ ⋆⊑ ⟩ | ⋆⊑ | l⊑l {low} | low ?? p    {- impossible -}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id⨾? _ _ ⟩ | ⋆⊑ | l⊑l {high} | high ?? p =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾? ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castl _ () ⋆⊑) ⋆⊑ ⋆⊑ ⟩ | ⋆⊑ | l⊑l {high} | high ?? p {- impossible -}
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () ⋆⊑) _ _ ⟩ | ⋆⊑ | l⊑l {high} | high ?? p {- impossible -}
... | ⟨ c̅ₙ ⨾ low  ! , inj v , c̅↠c̅ₙ⨾! , ⊑-cast  c̅ₙ⊑id () ⋆⊑ ⟩           | ⋆⊑ | l⊑l {high} | high ?? p {- impossible -}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () ⋆⊑) _ _ ⟩ | ⋆⊑ | l⊑l {low}  | low ??  p {- impossible -}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ⨾! , ⊑-cast  c̅ₙ⊑id () ⋆⊑ ⟩           | ⋆⊑ | l⊑l {low}  | low ??  p {- impossible -}
catchup-to-id⨾? c̅ (⊑-castr c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup-to-id c̅ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ = ⟨ c̅ₙ , v , c̅↠c̅ₙ , ⊑-castr c̅ₙ⊑id ⋆⊑ ⋆⊑ ⟩


catchup-to-↑ : ∀ {g₁ g₂ g′}
  → (c̅   : CoercionExp g₁ ⇒ g₂   )
  → (c̅ₙ′ : CoercionExp g′ ⇒ l low)
  → 𝒱 c̅ₙ′
  → ⊢ c̅ ⊑ c̅ₙ′ ⨾ ↑
    -----------------------------------------------------
  → ∃[ c̅ₙ ] (𝒱 c̅ₙ) × (c̅ —↠ c̅ₙ) × (⊢ c̅ₙ ⊑ c̅ₙ′ ⨾ ↑)
catchup-to-↑ (c̅ ⨾ id ⋆) (id (l low)) id (⊑-cast c̅⊑id ⋆⊑ ⋆⊑)
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , ⊑-castr c̅ₙ⊑id ⋆⊑ ⋆⊑ ⟩
catchup-to-↑ (c̅ ⨾ ↑) (id (l low)) id (⊑-cast c̅⊑id l⊑l l⊑l)
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , up v , plug-cong c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
catchup-to-↑ (c̅ ⨾ low !) (id (l low)) id (⊑-cast c̅⊑id l⊑l ⋆⊑)
  with catchup-to-id c̅ c̅⊑id
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id ⟩ =
  ⟨ c̅ₙ ⨾ low ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑id l⊑l ⋆⊑ ⟩
catchup-to-↑ (c̅ ⨾ c) (id (l low)) id (⊑-cast c̅⊑c̅ₙ′ ⋆⊑ l⊑l)
  with catchup-to-id c̅ c̅⊑c̅ₙ′ | c
... | ⟨ id ⋆ , id , c̅↠c̅ₙ , ⊑-id ⋆⊑ ⟩ | high ?? p =
  ⟨ id ⋆ ⨾ high ?? p , id⨾? , plug-cong c̅↠c̅ₙ , ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id l⊑l ⋆⊑ ⟩ | high ?? p =
  ⟨ c̅ₙ ⨾ ↑ , up v , ↠-trans (plug-cong c̅↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castl _ () _ ⟩ | high ?? p                                  {- impossible -}
catchup-to-↑ (c̅ ⨾ id ⋆) (id ⋆ ⨾ low ?? p) id⨾? (⊑-cast c̅⊑id⨾? ⋆⊑ ⋆⊑)
  with catchup-to-id⨾? c̅ c̅⊑id⨾?
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id⨾? ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , ⊑-castr c̅ₙ⊑id⨾? ⋆⊑ ⋆⊑ ⟩
catchup-to-↑ (c̅ ⨾ ↑) (id ⋆ ⨾ low ?? p) id⨾? (⊑-cast c̅⊑id⨾? l⊑l l⊑l)
  with catchup-to-id⨾? c̅ c̅⊑id⨾?
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id⨾? ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , up v , plug-cong c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
catchup-to-↑ (c̅ ⨾ low !) (id ⋆ ⨾ low ?? p) id⨾? (⊑-cast c̅⊑id⨾? l⊑l ⋆⊑)
  with catchup-to-id⨾? c̅ c̅⊑id⨾?
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id⨾? ⟩ =
  ⟨ c̅ₙ ⨾ low ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑id⨾? l⊑l ⋆⊑ ⟩
catchup-to-↑ (c̅ ⨾ high ?? p) (id ⋆ ⨾ low ?? q) id⨾? (⊑-cast c̅⊑id⨾? ⋆⊑ l⊑l)
  with catchup-to-id⨾? c̅ c̅⊑id⨾?
... | ⟨ id ⋆ , id , c̅↠c̅ₙ , c̅ₙ⊑id⨾? ⟩ =
  ⟨ id ⋆ ⨾ (high ?? p) , id⨾? , plug-cong c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑id⨾? ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castl c̅ₙ⊑id⨾? l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , up v , ↠-trans (plug-cong c̅↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) _ _ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑ ⟩
catchup-to-↑ (c̅ ⨾ id ⋆) (id (l low)) id (⊑-castl c̅⊑id⨾↑ ⋆⊑ ⋆⊑)
  with catchup-to-↑ c̅ _ id c̅⊑id⨾↑
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id⨾↑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
catchup-to-↑ (c̅ ⨾ id (l high)) (id (l low)) id (⊑-castl c̅⊑id⨾↑ l⊑l l⊑l)
  with catchup-to-↑ c̅ _ id c̅⊑id⨾↑
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id⨾↑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
catchup-to-↑ (c̅ ⨾ high !) (id (l low)) id (⊑-castl c̅⊑id⨾↑ l⊑l ⋆⊑)
  with catchup-to-↑ c̅ _ id c̅⊑id⨾↑
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑id⨾↑ ⟩ =
  ⟨ c̅ₙ ⨾ high ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id⨾↑ l⊑l ⋆⊑ ⟩
catchup-to-↑ (c̅ ⨾ high ?? p) (id (l low)) id (⊑-castl c̅⊑id⨾↑ ⋆⊑ l⊑l)
  with catchup c̅ _ (up id) c̅⊑id⨾↑
... | ⟨ id ⋆ , id , c̅↠id , ⊑-castr (⊑-id ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , id⨾? , plug-cong c̅↠id , ⊑-cast (⊑-id ⋆⊑) ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑id _ _ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , up v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ⨾! , ⊑-castr (⊑-castl c̅ₙ⊑id l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , up v , ↠-trans (plug-cong c̅↠c̅ₙ⨾!) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑id⨾↑ l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑id⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castl _ () _) _ _ ⟩
catchup-to-↑ (c̅ ⨾ id (l high)) (id ⋆ ⨾ low ?? p) id⨾? (⊑-castl c̅⊑c̅ₙ′⨾↑ l⊑l l⊑l)
  with catchup-to-↑ c̅ _ id⨾? c̅⊑c̅ₙ′⨾↑
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′⨾↑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′⨾↑ ⟩
catchup-to-↑ (c̅ ⨾ id ⋆) (id ⋆ ⨾ low ?? p) id⨾? (⊑-castl c̅⊑c̅ₙ′⨾↑ ⋆⊑ ⋆⊑)
  with catchup-to-↑ c̅ _ id⨾? c̅⊑c̅ₙ′⨾↑
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′⨾↑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′⨾↑ ⟩
catchup-to-↑ (c̅ ⨾ high !) (id ⋆ ⨾ low ?? p) id⨾? (⊑-castl c̅⊑c̅ₙ′⨾↑ l⊑l ⋆⊑)
  with catchup-to-↑ c̅ _ id⨾? c̅⊑c̅ₙ′⨾↑
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′⨾↑ ⟩ =
  ⟨ c̅ₙ ⨾ high ! , inj v , plug-cong c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅ₙ′⨾↑ l⊑l ⋆⊑ ⟩
catchup-to-↑ (c̅ ⨾ high ?? p) (id ⋆ ⨾ low ?? q) id⨾? (⊑-castl c̅⊑c̅ₙ′⨾↑ ⋆⊑ l⊑l)
  with catchup-to-↑ c̅ _ id⨾? c̅⊑c̅ₙ′⨾↑
... | ⟨ id ⋆ , id , c̅↠c̅ₙ , id⊑id⨾?⨾↑ ⟩ =
  ⟨ id ⋆ ⨾ high ?? p , id⨾? , plug-cong c̅↠c̅ₙ , ⊑-castl id⊑id⨾?⨾↑ ⋆⊑ l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-cast c̅ₙ⊑id⨾? l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , up v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castl c̅ₙ⊑id⨾? l⊑l ⋆⊑) ⋆⊑ ⋆⊑ ⟩ =
  ⟨ c̅ₙ ⨾ ↑ , up v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-↑ v ⟩ _ ∎) , ⊑-cast c̅ₙ⊑id⨾? l⊑l l⊑l ⟩
... | ⟨ c̅ₙ ⨾ low ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩                 {- impossible -}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castl c̅ₙ⊑c̅ₙ′⨾↑ l⊑l ⋆⊑ ⟩ =
  ⟨ c̅ₙ , v , ↠-trans (plug-cong c̅↠c̅ₙ) (_ —→⟨ ?-id v ⟩ _ ∎) , c̅ₙ⊑c̅ₙ′⨾↑ ⟩
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-cast _ () _) ⋆⊑ ⋆⊑ ⟩                                 {- impossible -}
... | ⟨ c̅ₙ ⨾ high ! , inj v , c̅↠c̅ₙ , ⊑-castr (⊑-castr (⊑-castl _ () _) ⋆⊑ ⋆⊑) ⋆⊑ ⋆⊑ ⟩                {- impossible -}
catchup-to-↑ c̅ c̅ₙ′ v′ (⊑-castr c̅⊑c̅ₙ′ ⋆⊑ ⋆⊑)
  with catchup c̅ c̅ₙ′ v′ c̅⊑c̅ₙ′
... | ⟨ c̅ₙ , v , c̅↠c̅ₙ , c̅ₙ⊑c̅ₙ′ ⟩  =
  ⟨ c̅ₙ , v , c̅↠c̅ₙ , ⊑-castr c̅ₙ⊑c̅ₙ′ ⋆⊑ ⋆⊑ ⟩

catchup c̅ (id g′) id c̅⊑id = catchup-to-id c̅ c̅⊑id
catchup c̅ (c̅ₙ′ ⨾ ℓ′ !) (inj v′) c̅⊑c̅′ = catchup-to-inj c̅ c̅ₙ′ v′ c̅⊑c̅′
catchup c̅ (id ⋆ ⨾ ℓ′ ?? p) id⨾? c̅⊑c̅′ = catchup-to-id⨾? c̅ c̅⊑c̅′
catchup c̅ (c̅ₙ′ ⨾ ↑)   (up  v′) c̅⊑c̅′ = catchup-to-↑ c̅ c̅ₙ′ v′ c̅⊑c̅′
