module BigStepErased where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC

infix 2 _∣_⊢_⇓ₑ_∣_
data _∣_⊢_⇓ₑ_∣_ : HalfHeap → StaticLabel → (M V : Term) → HalfHeap → Set

⇓ₑ-value : ∀ {μ μ′ pc M V} → μ ∣ pc ⊢ M ⇓ₑ V ∣ μ′ → Value V

{- runs on erased terms -}
data _∣_⊢_⇓ₑ_∣_ where

  ⇓ₑ-val : ∀ {μ pc V}
    → Value V
      --------------------------- Value
    → μ ∣ pc ⊢ V ⇓ₑ V ∣ μ

  ⇓ₑ-app : ∀ {μ μ₁ μ₂ μ₃ pc pc′ L M N V W A}
    → μ  ∣ pc ⊢ L       ⇓ₑ ƛ[ pc′ ] A ˙ N of low ∣ μ₁
    → μ₁ ∣ pc ⊢ M       ⇓ₑ V ∣ μ₂
    → μ₂ ∣ pc ⊢ N [ V ] ⇓ₑ W ∣ μ₃
      ---------------------------------------- Application
    → μ  ∣ pc ⊢ L · M   ⇓ₑ W ∣ μ₃

  ⇓ₑ-app-● : ∀ {μ μ₁ μ₂ pc L M V}
    → μ  ∣ pc ⊢ L       ⇓ₑ ● ∣ μ₁
    → μ₁ ∣ pc ⊢ M       ⇓ₑ V  ∣ μ₂
      ---------------------------------------- Application●
    → μ  ∣ pc ⊢ L · M   ⇓ₑ ● ∣ μ₂

  ⇓ₑ-if-true : ∀ {μ μ₁ μ₂ pc L M N V A}
    → μ  ∣ pc ⊢ L          ⇓ₑ $ true of low ∣ μ₁
    → μ₁ ∣ pc ⊢ M          ⇓ₑ V ∣ μ₂
      ------------------------------------------------ IfTrue
    → μ  ∣ pc ⊢ if L A M N ⇓ₑ V ∣ μ₂

  ⇓ₑ-if-false : ∀ {μ μ₁ μ₂ pc L M N V A}
    → μ  ∣ pc ⊢ L          ⇓ₑ $ false of low ∣ μ₁
    → μ₁ ∣ pc ⊢ N          ⇓ₑ V ∣ μ₂
      ------------------------------------------------ IfFalse
    → μ  ∣ pc ⊢ if L A M N ⇓ₑ V ∣ μ₂

  ⇓ₑ-if-● : ∀ {μ μ₁ pc L M N A}
    → μ  ∣ pc ⊢ L          ⇓ₑ ● ∣ μ₁
      ------------------------------------------------ If●
    → μ  ∣ pc ⊢ if L A M N ⇓ₑ ● ∣ μ₁

  ⇓ₑ-let : ∀ {μ μ₁ μ₂ pc M N V W}
    → μ  ∣ pc ⊢ M        ⇓ₑ V ∣ μ₁
    → μ₁ ∣ pc ⊢ N [ V ]  ⇓ₑ W ∣ μ₂
      ----------------------------------------- Let
    → μ  ∣ pc ⊢ `let M N ⇓ₑ W ∣ μ₂

  ⇓ₑ-ref? : ∀ {μ μ₁ pc M V n}
    → (⇓V : μ ∣ pc ⊢ M ⇓ₑ V ∣ μ₁)
    → n ≡ length μ₁
    → pc ≼ low
      -------------------------------------------------------------------------------------- RefNSU
    → μ ∣ pc ⊢ ref?[ low ] M ⇓ₑ addr (a[ low ] n) of low ∣ ⟨ n , V & ⇓ₑ-value ⇓V ⟩ ∷ μ₁

  ⇓ₑ-ref?-● : ∀ {μ μ₁ pc M V}
    → (⇓V : μ ∣ pc ⊢ M ⇓ₑ V ∣ μ₁)
      -------------------------------------------------------------------------------------- RefNSU●
    → μ ∣ pc ⊢ ref?[ high ] M ⇓ₑ ● ∣ μ₁ {- skip creation -}

  ⇓ₑ-ref : ∀ {μ μ₁ pc M V n}
    → (⇓V : μ ∣ pc ⊢ M ⇓ₑ V ∣ μ₁)
    → n ≡ length μ₁
      -------------------------------------------------------------------------------------- Ref
    → μ ∣ pc ⊢ ref[ low ] M ⇓ₑ addr (a[ low ] n) of low ∣ ⟨ n , V & ⇓ₑ-value ⇓V ⟩ ∷ μ₁

  ⇓ₑ-ref-● : ∀ {μ μ₁ pc M V}
    → (⇓V : μ ∣ pc ⊢ M ⇓ₑ V ∣ μ₁)
      -------------------------------------------------------------------------------------- Ref●
    → μ ∣ pc ⊢ ref[ high ] M ⇓ₑ ● ∣ μ₁ {- skip creation -}

  ⇓ₑ-deref : ∀ {μ μ₁ pc M V v n}
    → μ ∣ pc ⊢ M ⇓ₑ addr (a[ low ] n) of low ∣ μ₁
    → find _≟_ μ₁ n ≡ just (V & v)
      ---------------------------------- Deref
    → μ ∣ pc ⊢ ! M ⇓ₑ V ∣ μ₁

  ⇓ₑ-deref-● : ∀ {μ μ₁ pc M}
    → μ ∣ pc ⊢ M   ⇓ₑ ● ∣ μ₁
      ----------------------------------------- Deref●
    → μ ∣ pc ⊢ ! M ⇓ₑ ● ∣ μ₁

  ⇓ₑ-assign? : ∀ {μ μ₁ μ₂ pc L M V n}
    → μ  ∣ pc ⊢ L      ⇓ₑ addr (a[ low ] n) of low ∣ μ₁
    → (⇓V : μ₁ ∣ pc ⊢ M ⇓ₑ V ∣ μ₂)
    → pc ≼ low
      -------------------------------------------------------------------------- AssignNSU
    → μ ∣ pc ⊢ L :=? M ⇓ₑ $ tt of low ∣ ⟨ n , V & ⇓ₑ-value ⇓V ⟩ ∷ μ₂

  ⇓ₑ-assign?-● : ∀ {μ μ₁ μ₂ pc L M V}
    → μ  ∣ pc ⊢ L       ⇓ₑ ● ∣ μ₁
    → μ₁ ∣ pc ⊢ M       ⇓ₑ V  ∣ μ₂
      -------------------------------------------------------- AssignNSU●
    → μ  ∣ pc ⊢ L :=? M ⇓ₑ $ tt of low ∣ μ₂ {- skip assignment -}

  ⇓ₑ-assign : ∀ {μ μ₁ μ₂ pc L M V n}
    → μ  ∣ pc ⊢ L      ⇓ₑ addr (a[ low ] n) of low ∣ μ₁
    → (⇓V : μ₁ ∣ pc ⊢ M ⇓ₑ V ∣ μ₂)
      -------------------------------------------------------------------------- Assign
    → μ  ∣ pc ⊢ L := M ⇓ₑ $ tt of low ∣ ⟨ n , V & ⇓ₑ-value ⇓V ⟩ ∷ μ₂

  ⇓ₑ-assign-● : ∀ {μ μ₁ μ₂ pc L M V}
    → μ  ∣ pc ⊢ L      ⇓ₑ ● ∣ μ₁
    → μ₁ ∣ pc ⊢ M      ⇓ₑ V  ∣ μ₂
      -------------------------------------------------------- Assign●
    → μ  ∣ pc ⊢ L := M ⇓ₑ $ tt of low ∣ μ₂ {- skip assignment -}


⇓ₑ-value (⇓ₑ-val v) = v
⇓ₑ-value (⇓ₑ-app _ _ ⇓V) = ⇓ₑ-value ⇓V
⇓ₑ-value (⇓ₑ-app-● _ _) = V-●
⇓ₑ-value (⇓ₑ-if-true  _ ⇓V) = ⇓ₑ-value ⇓V
⇓ₑ-value (⇓ₑ-if-false _ ⇓V) = ⇓ₑ-value ⇓V
⇓ₑ-value (⇓ₑ-if-● ⇓V) = V-●
⇓ₑ-value (⇓ₑ-let _ ⇓V) = ⇓ₑ-value ⇓V
⇓ₑ-value (⇓ₑ-ref? _ _ _) = V-addr
⇓ₑ-value (⇓ₑ-ref?-● _) = V-●
⇓ₑ-value (⇓ₑ-ref    _ _) = V-addr
⇓ₑ-value (⇓ₑ-ref-● _) = V-●
⇓ₑ-value (⇓ₑ-deref {v = v} _ _) = v
⇓ₑ-value (⇓ₑ-deref-●        _) = V-●
⇓ₑ-value (⇓ₑ-assign?     _ _ _) = V-const
⇓ₑ-value (⇓ₑ-assign?-●    _ _) = V-const
⇓ₑ-value (⇓ₑ-assign        _ _) = V-const
⇓ₑ-value (⇓ₑ-assign-●     _ _) = V-const


V⇓ₑV : ∀ {μ μ′ pc V W}
  → μ ∣ pc ⊢ V ⇓ₑ W ∣ μ′
  → Value V
    ---------------------------
  → V ≡ W × μ ≡ μ′
V⇓ₑV (⇓ₑ-val _) v = ⟨ refl , refl ⟩


{- ⇓ₑ is transitive -}
⇓ₑ-trans : ∀ {μ μ₁ μ₂ pc M V W}
  → μ  ∣ pc ⊢ M ⇓ₑ V ∣ μ₁
  → μ₁ ∣ pc ⊢ V ⇓ₑ W ∣ μ₂
    ---------------------------
  → μ  ∣ pc ⊢ M ⇓ₑ W ∣ μ₂
⇓ₑ-trans M⇓V V⇓W with V⇓ₑV V⇓W (⇓ₑ-value M⇓V)
... | ⟨ refl , refl ⟩ = M⇓V


{- a few inversion lemmas about ⇓ₑ -}
⇓ₑ-app-●-inv : ∀ {μ μ′ pc V W}
  → μ ∣ pc ⊢ ● · V ⇓ₑ W ∣ μ′
  → Value V
    ---------------------------
  → W ≡ ● × μ ≡ μ′
⇓ₑ-app-●-inv (⇓ₑ-app-● ●⇓● V⇓V) v
  with V⇓ₑV ●⇓● V-● | V⇓ₑV V⇓V v
... | ⟨ refl , refl ⟩ | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩

⇓ₑ-app-inv : ∀ {μ μ′ pc pc′ N V W A}
  → μ ∣ pc ⊢ ƛ[ pc′ ] A ˙ N of low · V ⇓ₑ W ∣ μ′
  → Value V
    ------------------------------------------
  → μ ∣ pc ⊢ N [ V ] ⇓ₑ W ∣ μ′
⇓ₑ-app-inv (⇓ₑ-app ƛN⇓ƛN V⇓V N[V]⇓W) v
  with V⇓ₑV ƛN⇓ƛN V-ƛ | V⇓ₑV V⇓V v
... | ⟨ refl , refl ⟩ | ⟨ refl , refl ⟩ = N[V]⇓W

⇓ₑ-assign-●-inv : ∀ {μ μ′ pc M V}
  → μ ∣ pc ⊢ ● := M ⇓ₑ V ∣ μ′
    ---------------------------
  → V ≡ $ tt of low × ∃[ W ] (μ ∣ pc ⊢ M ⇓ₑ W ∣ μ′)
⇓ₑ-assign-●-inv (⇓ₑ-assign-● ●⇓● M⇓W)
  with V⇓ₑV ●⇓● V-●
... | ⟨ refl , refl ⟩ = ⟨ refl , _ , M⇓W ⟩

⇓ₑ-assign-inv : ∀ {μ μ′ pc M V n}
  → μ ∣ pc ⊢ (addr a[ low ] n of low) := M ⇓ₑ V ∣ μ′
    -----------------------------------------------------------
  → V ≡ $ tt of low × ∃[ W ] ∃[ w ] ∃[ μ″ ] (μ ∣ pc ⊢ M ⇓ₑ W ∣ μ″) × (μ′ ≡ ⟨ n , W & w ⟩ ∷ μ″)
⇓ₑ-assign-inv (⇓ₑ-assign a⇓a M⇓W)
  with V⇓ₑV a⇓a V-addr
... | ⟨ refl , refl ⟩ = ⟨ refl , _ , ⇓ₑ-value M⇓W , _ , M⇓W , refl ⟩

⇓ₑ-assign?-●-inv : ∀ {μ μ′ pc M V}
  → μ ∣ pc ⊢ ● :=? M ⇓ₑ V ∣ μ′
    ---------------------------
  → V ≡ $ tt of low × ∃[ W ] (μ ∣ pc ⊢ M ⇓ₑ W ∣ μ′)
⇓ₑ-assign?-●-inv (⇓ₑ-assign?-● ●⇓● M⇓W)
  with V⇓ₑV ●⇓● V-●
... | ⟨ refl , refl ⟩ = ⟨ refl , _ , M⇓W ⟩

⇓ₑ-assign?-inv : ∀ {μ μ′ pc M V n}
  → μ ∣ pc ⊢ (addr a[ low ] n of low) :=? M ⇓ₑ V ∣ μ′
    -----------------------------------------------------------
  → V ≡ $ tt of low × pc ≼ low × ∃[ W ] ∃[ w ] ∃[ μ″ ] (μ ∣ pc ⊢ M ⇓ₑ W ∣ μ″) × (μ′ ≡ ⟨ n , W & w ⟩ ∷ μ″)
⇓ₑ-assign?-inv (⇓ₑ-assign? a⇓a M⇓W pc≼low)
  with V⇓ₑV a⇓a V-addr
... | ⟨ refl , refl ⟩ = ⟨ refl , pc≼low , _ , ⇓ₑ-value M⇓W , _ , M⇓W , refl ⟩

⇓ₑ-deref-●-inv : ∀ {μ μ′ pc V}
  → μ ∣ pc ⊢ ! ● ⇓ₑ V ∣ μ′
    ---------------------------
  → V ≡ ● × μ ≡ μ′
⇓ₑ-deref-●-inv (⇓ₑ-deref-● ●⇓●) with V⇓ₑV ●⇓● V-●
... | ⟨ refl , refl ⟩ = ⟨ refl , refl ⟩

⇓ₑ-deref-inv : ∀ {μ μ′ pc V n}
  → μ ∣ pc ⊢ ! (addr a[ low ] n of low) ⇓ₑ V ∣ μ′
    --------------------------------------------------
  → (∃[ v ] find _≟_ μ n ≡ just (V & v)) × μ ≡ μ′
⇓ₑ-deref-inv (⇓ₑ-deref {v = v} a⇓a eq) with V⇓ₑV a⇓a V-addr
... | ⟨ refl , refl ⟩ = ⟨ ⟨ v , eq ⟩ , refl ⟩
