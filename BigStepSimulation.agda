module BigStepSimulation where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import HeapTyping
open import BigStep
open import BigStepErased
open import Erasure

open import BigStepPreservation
open import HeapSecure
open import ApplyCastErasure
open import ProxyEliminationErasure
open import CanonicalErased

open import ErasureSubstitution public


sim : ∀ {Σ gc pc A M V μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → μ ∣ pc ⊢ M ⇓ V ∣ μ′
    ----------------------------------------------------------------------------------
  → erase-μ μ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
sim ⊢M ⊢μ pc≾gc (⇓-val v) = (⇓ₑ-val (erase-val-value v))
sim {pc = pc} {μ′ = μ′} (⊢app ⊢L ⊢M) ⊢μ pc≾gc
    (⇓-app {L = L} {M} {N} {V} {W} {ℓ = ℓ} L⇓ƛN M⇓V N[V]⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN
... | ⟨ Σ₁ , Σ₁⊇Σ  , ⊢ƛN , ⊢μ₁ ⟩
  with ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩
  with ℓ
...   | low
  rewrite stamp-val-low (⇓-value N[V]⇓W) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-app (sim ⊢L ⊢μ pc≾gc L⇓ƛN) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V) ϵN[ϵV]⇓ϵW
  where
  ϵN[ϵV]⇓ϵW : _ ∣ pc ⊢ erase N [ erase V ] ⇓ₑ erase W ∣ _
  ϵN[ϵV]⇓ϵW rewrite sym (substitution-erase N V) =
    case canonical-fun ⊢ƛN V-ƛ of λ where
    (Fun-ƛ ⊢N (<:-ty _ (<:-fun gc⋎g<:pc′ A₁<:A _))) →
      case ⟨ pc≾gc , consis-join-<:ₗ-inv gc⋎g<:pc′ ⟩ of λ where
      ⟨ ≾-l pc≼gc , <:-l gc≼pc′ , _ ⟩ →
        sim (substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁)
                               (⊢value-pc (⊢sub ⊢V A₁<:A) (⇓-value M⇓V)))
            ⊢μ₂ (≾-l (≼-trans pc≼gc gc≼pc′)) N[V]⇓W
...   | high
  rewrite erase-stamp-high (⇓-value N[V]⇓W) | ℓ⋎high≡high {pc} =
  ⇓ₑ-app-● (sim ⊢L ⊢μ pc≾gc L⇓ƛN) ϵM⇓ϵV
  where
  ϵμ₂≡ϵμ′ =
    case canonical-fun ⊢ƛN V-ƛ of λ where
    (Fun-ƛ ⊢N (<:-ty (<:-l h≼h) (<:-fun gc⋎g<:pc′ A₁<:A _))) →
      case consis-join-<:ₗ-inv gc⋎g<:pc′ of λ where
      ⟨ <:-l gc≼pc′ , <:-l h≼h ⟩ →
        heap-relate (substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁)
                    (⊢value-pc (⊢sub ⊢V A₁<:A) (⇓-value M⇓V))) ⊢μ₂ (≾-l h≼h) N[V]⇓W
  ϵM⇓ϵV : _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
  ϵM⇓ϵV = subst (λ □ → _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ □)
             ϵμ₂≡ϵμ′ (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V)
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢if {g = g} ⊢L ⊢M ⊢N) ⊢μ pc≾gc
    (⇓-if-true  {μ₁ = μ₁} {L = L} {M} {N} {V} {ℓ = ℓ} L⇓true  M⇓V)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true
... | ⟨ Σ₁ , Σ₁⊇Σ  , ⊢true , ⊢μ₁ ⟩
  with ℓ
... | low  rewrite stamp-val-low (⇓-value M⇓V) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-if-true (sim ⊢L ⊢μ pc≾gc L⇓true) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc⋎g M⇓V)
  where
  pc⋎low≾gc⋎g : (l pc) ⋎̃ (l low) ≾ gc ⋎̃ g
  pc⋎low≾gc⋎g = consis-join-≾ pc≾gc (low≾ g)
  pc≾gc⋎g : l pc ≾ gc ⋎̃ g
  pc≾gc⋎g = subst (λ □ → □ ≾ gc ⋎̃ g) (g⋎̃low≡g {l pc}) pc⋎low≾gc⋎g
... | high rewrite erase-stamp-high (⇓-value M⇓V) | ℓ⋎high≡high {pc} =
  ⇓ₑ-if-● ϵL⇓●
  where
  ϵμ₁≡ϵμ′ : erase-μ μ₁ ≡ erase-μ μ′
  ϵμ₁≡ϵμ′ =
    case canonical-const ⊢true V-const of λ where
    (Const-base h≼h) → heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ (consis-join-≾ (low≾ gc) (≾-l h≼h)) M⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ′
  ϵL⇓● rewrite sym ϵμ₁≡ϵμ′ = sim ⊢L ⊢μ pc≾gc L⇓true
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢if {g = g} ⊢L ⊢M ⊢N) ⊢μ pc≾gc
    (⇓-if-false {μ₁ = μ₁} {L = L} {M} {N} {V} {ℓ = ℓ} L⇓false  N⇓V)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false
... | ⟨ Σ₁ , Σ₁⊇Σ  , ⊢false , ⊢μ₁ ⟩
  with ℓ
... | low  rewrite stamp-val-low (⇓-value N⇓V) | ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-if-false (sim ⊢L ⊢μ pc≾gc L⇓false) (sim (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ pc≾gc⋎g N⇓V)
  where
  pc⋎low≾gc⋎g : (l pc) ⋎̃ (l low) ≾ gc ⋎̃ g
  pc⋎low≾gc⋎g = consis-join-≾ pc≾gc (low≾ g)
  pc≾gc⋎g : l pc ≾ gc ⋎̃ g
  pc≾gc⋎g = subst (λ □ → □ ≾ gc ⋎̃ g) (g⋎̃low≡g {l pc}) pc⋎low≾gc⋎g
... | high rewrite erase-stamp-high (⇓-value N⇓V) | ℓ⋎high≡high {pc} =
  ⇓ₑ-if-● ϵL⇓●
  where
  ϵμ₁≡ϵμ′ : erase-μ μ₁ ≡ erase-μ μ′
  ϵμ₁≡ϵμ′ =
    case canonical-const ⊢false V-const of λ where
    (Const-base h≼h) → heap-relate (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ (consis-join-≾ (low≾ gc) (≾-l h≼h)) N⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ′
  ϵL⇓● rewrite sym ϵμ₁≡ϵμ′ = sim ⊢L ⊢μ pc≾gc L⇓false
sim {pc = pc} (⊢let ⊢M ⊢N) ⊢μ pc≾gc (⇓-let {M = M} {N} {V} {W} M⇓V N[V]⇓W)
  with ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ =
  ⇓ₑ-let (sim ⊢M ⊢μ pc≾gc M⇓V) ϵN[ϵV]⇓ϵW
  where
  ϵN[ϵV]⇓ϵW : _ ∣ pc ⊢ erase N [ erase V ] ⇓ₑ erase W ∣ _
  ϵN[ϵV]⇓ϵW rewrite sym (substitution-erase N V) =
    let v = ⇓-value M⇓V in
    sim (substitution-pres (relax-Σ ⊢N Σ₁⊇Σ) (⊢value-pc ⊢V v)) ⊢μ₁ pc≾gc N[V]⇓W
sim (⊢ref? ⊢M) ⊢μ pc≾gc (⇓-ref? {μ} {μ₁} {ℓ = low} M⇓V fresh pc≼ℓ)
  rewrite erase-μᴸ-length (proj₁ μ₁) =
  ⇓ₑ-ref? (sim ⊢M ⊢μ pc≾gc M⇓V) fresh pc≼ℓ
sim (⊢ref? ⊢M) ⊢μ pc≾gc (⇓-ref? {ℓ = high} M⇓V fresh pc≼ℓ) =
  ⇓ₑ-ref?-● (sim ⊢M ⊢μ pc≾gc M⇓V)
sim (⊢ref ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-ref {μ} {μ₁} {ℓ = low} M⇓V fresh)
  rewrite erase-μᴸ-length (proj₁ μ₁) =
  ⇓ₑ-ref (sim ⊢M ⊢μ pc≾gc M⇓V) fresh
sim (⊢ref ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-ref {ℓ = high} M⇓V fresh) =
  ⇓ₑ-ref-● (sim ⊢M ⊢μ pc≾gc M⇓V)
sim {μ′ = ⟨ μᴸ , μᴴ ⟩} (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = low} {low} M⇓a eq)
  rewrite stamp-val-low v =
  ⇓ₑ-deref {v = erase-val-value v} (sim ⊢M ⊢μ pc≾gc M⇓a)
            (erase-μ-lookup-low {μᴸ} {μᴴ} {v = v} eq)
sim (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = low} {high} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim ⊢M ⊢μ pc≾gc M⇓a)
sim (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = high} {low} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim ⊢M ⊢μ pc≾gc M⇓a)
sim (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = high} {high} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim ⊢M ⊢μ pc≾gc M⇓a)
sim (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc (⇓-assign? {ℓ = ℓ} {ℓ₁} L⇓a M⇓V pc≼ℓ₁)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓a
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢a , ⊢μ₁ ⟩
  with ℓ | ℓ₁
...   | low | low =
  ⇓ₑ-assign? (sim ⊢L ⊢μ pc≾gc L⇓a) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V) pc≼ℓ₁
...   | low | high =
  ⇓ₑ-assign?-● (sim ⊢L ⊢μ pc≾gc L⇓a) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V)
...   | high | low =  {- impossible -}
 case canonical-ref ⊢a V-addr of λ where
 (Ref-addr eq₁ (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
   case <:-antisym A′<:A A<:A′ of λ where
   refl → contradiction ℓ≼ℓ′ λ ()  {- high ⋠ low -}
...   | high | high =
  ⇓ₑ-assign?-● (sim ⊢L ⊢μ pc≾gc L⇓a) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V)
sim (⊢assign ⊢L ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-assign {ℓ = ℓ} {ℓ₁} L⇓a M⇓V)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓a
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢a , ⊢μ₁ ⟩
  with ℓ | ℓ₁
...   | low | low =
  ⇓ₑ-assign (sim ⊢L ⊢μ pc≾gc L⇓a) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V)
...   | low | high =
  ⇓ₑ-assign-● (sim ⊢L ⊢μ pc≾gc L⇓a) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V)
...   | high | low =  {- impossible -}
 case canonical-ref ⊢a V-addr of λ where
 (Ref-addr eq₁ (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
   case <:-antisym A′<:A A<:A′ of λ where
   refl → contradiction ℓ≼ℓ′ λ ()  {- high ⋠ low -}
...   | high | high =
  ⇓ₑ-assign-● (sim ⊢L ⊢μ pc≾gc L⇓a) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V)
sim {pc = pc} (⊢cast ⊢M) ⊢μ pc≾gc (⇓-cast {M = M} {N} {V} {W} {c = c} a M⇓V V⟨c⟩↝N N⇓W)
  with ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ =
  ⇓ₑ-trans ϵM⇓ϵV ϵV⇓ϵW
  where
  ϵV≡ϵN : erase V ≡ erase N
  ϵV≡ϵN = applycast-erase V⟨c⟩↝N (error-not-⇓ N⇓W)
  v = ⇓-value M⇓V
  ϵM⇓ϵV = sim ⊢M ⊢μ pc≾gc M⇓V
  ϵN⇓ϵW = sim (applycast-pres (⊢value-pc ⊢V v) v a V⟨c⟩↝N) ⊢μ₁ pc≾gc N⇓W
  ϵV⇓ϵW : _ ∣ pc ⊢ erase V ⇓ₑ erase W ∣ _
  ϵV⇓ϵW rewrite ϵV≡ϵN = ϵN⇓ϵW
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc
    (⇓-if-cast-true {μ₁ = μ₁} {μ₂} {L = L} {M} {N} {V} {W} {A} {ℓ = ℓ} i L⇓true⟨c⟩ M⇓V V⋎ℓ⟨bc⟩⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢true⟨c⟩ , ⊢μ₁ ⟩
  with canonical-const ⊢true⟨c⟩ (⇓-value L⇓true⟨c⟩)
... | Const-inj _
  rewrite g⋎̃⋆≡⋆ {gc}
  with ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ ≾-⋆r M⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩
  with ℓ
...   | low
  rewrite stamp-val-low (⇓-value M⇓V) =
  ⇓ₑ-if-true ϵL⇓true (⇓ₑ-trans ϵM⇓ϵV ϵV⇓ϵW)
  where
  v = ⇓-value M⇓V
  ϵL⇓true : _ ∣ pc ⊢ erase L ⇓ₑ $ true of low ∣ _
  ϵL⇓true = sim ⊢L ⊢μ pc≾gc L⇓true⟨c⟩
  ϵM⇓ϵV : erase-μ μ₁ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ₂
  ϵM⇓ϵV = subst (λ □ → _ ∣ □ ⊢ _ ⇓ₑ _ ∣ _) (ℓ⋎low≡ℓ {pc})
                 (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ ≾-⋆r M⇓V)
  ϵV⇓ϵW : erase-μ μ₂ ∣ pc ⊢ erase V ⇓ₑ erase W ∣ erase-μ μ′
  ϵV⇓ϵW = sim (⊢cast (⊢value-pc (subst (λ □ → [] ; _ ; _ ; _ ⊢ V ⦂ □)
              (sym (stamp-low A)) ⊢V) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
...   | high = ϵif⇓ϵW
  where
  v = ⇓-value M⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ₁
  ϵL⇓● = sim ⊢L ⊢μ pc≾gc L⇓true⟨c⟩
  ●⇓ϵW : _ ∣ pc ⊢ ● ⇓ₑ erase W ∣ _
  ●⇓ϵW rewrite sym (erase-stamp-high v) =
    sim (⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
  ϵμ₁≡ϵμ₂ : erase-μ μ₁ ≡ erase-μ μ₂
  ϵμ₁≡ϵμ₂ rewrite ℓ⋎high≡high {pc} = heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ ≾-⋆r M⇓V
  ϵif⇓ϵW : erase-μ μ ∣ pc ⊢ erase (if L _ M N) ⇓ₑ erase W ∣ erase-μ μ′
  ϵif⇓ϵW with V⇓ₑV ●⇓ϵW V-●
  ... | ⟨ ●≡ϵW , ϵμ₂≡ϵμ′ ⟩
    rewrite sym ●≡ϵW | sym ϵμ₂≡ϵμ′ | sym ϵμ₁≡ϵμ₂ =
    ⇓ₑ-if-● ϵL⇓●
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc
    (⇓-if-cast-false {μ₁ = μ₁} {μ₂} {L = L} {M} {N} {V} {W} {A} {ℓ = ℓ} i L⇓false⟨c⟩ N⇓V V⋎ℓ⟨bc⟩⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢false⟨c⟩ , ⊢μ₁ ⟩
  with canonical-const ⊢false⟨c⟩ (⇓-value L⇓false⟨c⟩)
... | Const-inj _
  rewrite g⋎̃⋆≡⋆ {gc}
  with ⇓-preserve (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ ≾-⋆r N⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩
  with ℓ
...   | low
  rewrite stamp-val-low (⇓-value N⇓V) =
  ⇓ₑ-if-false ϵL⇓false (⇓ₑ-trans ϵN⇓ϵV ϵV⇓ϵW)
  where
  v = ⇓-value N⇓V
  ϵL⇓false : _ ∣ pc ⊢ erase L ⇓ₑ $ false of low ∣ _
  ϵL⇓false = sim ⊢L ⊢μ pc≾gc L⇓false⟨c⟩
  ϵN⇓ϵV : erase-μ μ₁ ∣ pc ⊢ erase N ⇓ₑ erase V ∣ erase-μ μ₂
  ϵN⇓ϵV = subst (λ □ → _ ∣ □ ⊢ _ ⇓ₑ _ ∣ _) (ℓ⋎low≡ℓ {pc})
                 (sim (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ ≾-⋆r N⇓V)
  ϵV⇓ϵW : erase-μ μ₂ ∣ pc ⊢ erase V ⇓ₑ erase W ∣ erase-μ μ′
  ϵV⇓ϵW = sim (⊢cast (⊢value-pc (subst (λ □ → [] ; _ ; _ ; _ ⊢ V ⦂ □)
              (sym (stamp-low A)) ⊢V) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
...   | high = ϵif⇓ϵW
  where
  v = ⇓-value N⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ₁
  ϵL⇓● = sim ⊢L ⊢μ pc≾gc L⇓false⟨c⟩
  ●⇓ϵW : _ ∣ pc ⊢ ● ⇓ₑ erase W ∣ _
  ●⇓ϵW rewrite sym (erase-stamp-high v) =
    sim (⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
  ϵμ₁≡ϵμ₂ : erase-μ μ₁ ≡ erase-μ μ₂
  ϵμ₁≡ϵμ₂ rewrite ℓ⋎high≡high {pc} = heap-relate (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ ≾-⋆r N⇓V
  ϵif⇓ϵW : erase-μ μ ∣ pc ⊢ erase (if L _ M N) ⇓ₑ erase W ∣ erase-μ μ′
  ϵif⇓ϵW with V⇓ₑV ●⇓ϵW V-●
  ... | ⟨ ●≡ϵW , ϵμ₂≡ϵμ′ ⟩
    rewrite sym ●≡ϵW | sym ϵμ₂≡ϵμ′ | sym ϵμ₁≡ϵμ₂ =
    ⇓ₑ-if-● ϵL⇓●
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢app ⊢L ⊢M) ⊢μ pc≾gc
    (⇓-fun-cast {μ₁ = μ₁} {μ₂} {L = L} {M} {V} {V′} {W} i L⇓V⟨c⟩ M⇓W elim⇓V′)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩
  with ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓W
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩
  with canonical-fun-erase ⊢V⟨c⟩ (⇓-value L⇓V⟨c⟩)
... | ⟨ _ , eq {- ƛ N ≡ ϵV -} , ϵ-fun-ƛ {pc′} {A} {N} ⟩ =
  ⇓ₑ-app ϵL⇓ƛN ϵM⇓ϵW (⇓ₑ-app-inv ƛN·ϵW⇓ϵV′ (erase-val-value w))
  where
  w = ⇓-value M⇓W
  ϵL⇓ϵV : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ erase V ∣ erase-μ μ₁
  ϵL⇓ϵV = sim ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
  ϵL⇓ƛN : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ƛ[ pc′ ] A ˙ N of low ∣ erase-μ μ₁
  ϵL⇓ƛN rewrite eq = ϵL⇓ϵV
  ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase M ⇓ₑ erase W ∣ erase-μ μ₂
  ϵM⇓ϵW = sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓W
  ϵelim⇓ϵV′ : erase-μ μ₂ ∣ pc ⊢ erase (elim-fun-proxy V W i pc) ⇓ₑ erase V′ ∣ erase-μ μ′
  ϵelim⇓ϵV′ =
    case ⇓-value L⇓V⟨c⟩ of λ where
    (V-cast v _) →
      sim (elim-fun-proxy-wt (⊢app (relax-Σ ⊢V⟨c⟩ Σ₂⊇Σ₁) ⊢W) v w i) ⊢μ₂ pc≾gc elim⇓V′
  ϵV·ϵW⇓ϵV′ : erase-μ μ₂ ∣ pc ⊢ erase V · erase W ⇓ₑ erase V′ ∣ erase-μ μ′
  ϵV·ϵW⇓ϵV′ rewrite sym (elim-fun-proxy-erase V W i pc refl (error-not-⇓ elim⇓V′)) = ϵelim⇓ϵV′
  ƛN·ϵW⇓ϵV′ : erase-μ μ₂ ∣ pc ⊢ ƛ[ pc′ ] A ˙ N of low · erase W ⇓ₑ erase V′ ∣ erase-μ μ′
  ƛN·ϵW⇓ϵV′ = subst (λ □ → _ ∣ _ ⊢ □ · _ ⇓ₑ _ ∣ _) (sym eq) ϵV·ϵW⇓ϵV′
... | ⟨ _ , eq {- ● ≡ ϵV -} , ϵ-fun-● ⟩ =
  subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym ϵV′≡●) ϵL·ϵM⇓●
  where
  w = ⇓-value M⇓W
  ϵL⇓ϵV : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ erase V ∣ erase-μ μ₁
  ϵL⇓ϵV = sim ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ₁
  ϵL⇓● = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym eq) ϵL⇓ϵV
  ϵelim⇓ϵV′ : erase-μ μ₂ ∣ pc ⊢ erase (elim-fun-proxy V W i pc) ⇓ₑ erase V′ ∣ erase-μ μ′
  ϵelim⇓ϵV′ =
    case ⇓-value L⇓V⟨c⟩ of λ where
    (V-cast v _) →
      sim (elim-fun-proxy-wt (⊢app (relax-Σ ⊢V⟨c⟩ Σ₂⊇Σ₁) ⊢W) v w i) ⊢μ₂ pc≾gc elim⇓V′
  ϵV·ϵW⇓ϵV′ : erase-μ μ₂ ∣ pc ⊢ erase V · erase W ⇓ₑ erase V′ ∣ erase-μ μ′
  ϵV·ϵW⇓ϵV′ rewrite sym (elim-fun-proxy-erase V W i pc refl (error-not-⇓ elim⇓V′)) = ϵelim⇓ϵV′
  ●·ϵW⇓ϵV′ : erase-μ μ₂ ∣ pc ⊢ ● · erase W ⇓ₑ erase V′ ∣ erase-μ μ′
  ●·ϵW⇓ϵV′ = subst (λ □ → _ ∣ _ ⊢ □ · _ ⇓ₑ _ ∣ _) (sym eq) ϵV·ϵW⇓ϵV′
  ϵV′≡●   = proj₁ (⇓ₑ-app-●-inv ●·ϵW⇓ϵV′ (erase-val-value w))
  ϵμ₂≡ϵμ′ = proj₂ (⇓ₑ-app-●-inv ●·ϵW⇓ϵV′ (erase-val-value w))
  ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase M ⇓ₑ erase W ∣ erase-μ μ₂
  ϵM⇓ϵW = sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓W
  ϵL·ϵM⇓● : erase-μ μ ∣ pc ⊢ erase L · erase M ⇓ₑ ● ∣ erase-μ μ′
  ϵL·ϵM⇓● rewrite sym ϵμ₂≡ϵμ′ = ⇓ₑ-app-● ϵL⇓● ϵM⇓ϵW
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢assign? ⊢L ⊢M) ⊢μ pc≾gc
    (⇓-assign?-cast {μ₁ = μ₁} {L = L} {M} {V} {W} i L⇓V⟨c⟩ elim⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩
  with canonical-ref-erase ⊢V⟨c⟩ (⇓-value L⇓V⟨c⟩)
... | ⟨ _ , eq {- ● ≡ ϵV -} , ϵ-ref-● ⟩ = ϵL:=ϵM⇓ϵW
  where
  ϵL⇓ϵV : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ erase V ∣ erase-μ μ₁
  ϵL⇓ϵV = sim ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
  ϵelim⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase (elim-ref-proxy V M i _:=?_) ⇓ₑ erase W ∣ erase-μ μ′
  ϵelim⇓ϵW =
    case ⇓-value L⇓V⟨c⟩ of λ where
    (V-cast v _) →
      sim (elim-ref-proxy-wt (⊢assign? ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ)) v i unchecked) ⊢μ₁ pc≾gc elim⇓W
  ϵV:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase V :=? erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵV:=ϵM⇓ϵW rewrite sym (elim-ref-proxy-erase V M i unchecked refl (error-not-⇓ elim⇓W)) =
    ϵelim⇓ϵW
  ●:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ ● :=? erase M ⇓ₑ erase W ∣ erase-μ μ′
  ●:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ □ :=? _ ⇓ₑ _ ∣ _) (sym eq) ϵV:=ϵM⇓ϵW
  ϵW≡tt : erase W ≡ $ tt of low
  ϵW≡tt  = proj₁ (⇓ₑ-assign?-●-inv ●:=ϵM⇓ϵW)
  ϵM⇓V′ = proj₂ (proj₂ (⇓ₑ-assign?-●-inv ●:=ϵM⇓ϵW))
  ϵL:=ϵM⇓tt : erase-μ μ ∣ pc ⊢ erase L :=? erase M ⇓ₑ $ tt of low ∣ erase-μ μ′
  ϵL:=ϵM⇓tt = ⇓ₑ-assign?-● (subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym eq) ϵL⇓ϵV) ϵM⇓V′
  ϵL:=ϵM⇓ϵW : erase-μ μ ∣ pc ⊢ erase L :=? erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵL:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym ϵW≡tt) ϵL:=ϵM⇓tt
... | ⟨ _ , eq {- a[ low ] n of low ≡ ϵV -} , ϵ-ref-addr {n} ⟩ = ϵL:=ϵM⇓ϵW
  where
  ϵL⇓ϵV : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ erase V ∣ erase-μ μ₁
  ϵL⇓ϵV = sim ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
  ϵelim⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase (elim-ref-proxy V M i _:=?_) ⇓ₑ erase W ∣ erase-μ μ′
  ϵelim⇓ϵW =
    case ⇓-value L⇓V⟨c⟩ of λ where
    (V-cast v _) →
      sim (elim-ref-proxy-wt (⊢assign? ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ)) v i unchecked) ⊢μ₁ pc≾gc elim⇓W
  ϵV:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase V :=? erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵV:=ϵM⇓ϵW rewrite sym (elim-ref-proxy-erase V M i unchecked refl (error-not-⇓ elim⇓W)) =
    ϵelim⇓ϵW
  a:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ (addr a[ low ] n of low) :=? erase M ⇓ₑ erase W ∣ erase-μ μ′
  a:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ □ :=? _ ⇓ₑ _ ∣ _) (sym eq) ϵV:=ϵM⇓ϵW
  ϵW≡tt : erase W ≡ $ tt of low
  ϵW≡tt = proj₁ (⇓ₑ-assign?-inv a:=ϵM⇓ϵW)
  pc≼low   = let ⟨ _ , pc≼low , _ ⟩ = ⇓ₑ-assign?-inv a:=ϵM⇓ϵW in pc≼low
  ϵM⇓V′   = let ⟨ _ , _ , W , w , μ″ , M⇓W , _ ⟩ = ⇓ₑ-assign?-inv a:=ϵM⇓ϵW in M⇓W
  ϵμ′≡a∷μ″ = let ⟨ _ , _ , W , w , μ″ , _ , μ′≡a∷μ″ ⟩ = ⇓ₑ-assign?-inv a:=ϵM⇓ϵW in μ′≡a∷μ″
  ϵL:=ϵM⇓tt : erase-μ μ ∣ pc ⊢ erase L :=? erase M ⇓ₑ $ tt of low ∣ erase-μ μ′
  ϵL:=ϵM⇓tt rewrite ϵμ′≡a∷μ″ = ⇓ₑ-assign? (subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym eq) ϵL⇓ϵV) ϵM⇓V′ pc≼low
  ϵL:=ϵM⇓ϵW : erase-μ μ ∣ pc ⊢ erase L :=? erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵL:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym ϵW≡tt) ϵL:=ϵM⇓tt
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢assign ⊢L ⊢M pc′≼ℓ) ⊢μ pc≾gc
    (⇓-assign-cast {μ₁ = μ₁} {L = L} {M} {V} {W} i L⇓V⟨c⟩ elim⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩
  with canonical-ref-erase ⊢V⟨c⟩ (⇓-value L⇓V⟨c⟩)
... | ⟨ _ , eq {- ● ≡ ϵV -} , ϵ-ref-● ⟩ = ϵL:=ϵM⇓ϵW
  where
  ϵL⇓ϵV : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ erase V ∣ erase-μ μ₁
  ϵL⇓ϵV = sim ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
  ϵelim⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase (elim-ref-proxy V M i _:=_) ⇓ₑ erase W ∣ erase-μ μ′
  ϵelim⇓ϵW =
    case ⇓-value L⇓V⟨c⟩ of λ where
    (V-cast v _) →
      sim (elim-ref-proxy-wt (⊢assign ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ) pc′≼ℓ) v i static) ⊢μ₁ pc≾gc elim⇓W
  ϵV:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase V := erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵV:=ϵM⇓ϵW rewrite sym (elim-ref-proxy-erase V M i static refl (error-not-⇓ elim⇓W)) =
    ϵelim⇓ϵW
  ●:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ ● := erase M ⇓ₑ erase W ∣ erase-μ μ′
  ●:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ □ := _ ⇓ₑ _ ∣ _) (sym eq) ϵV:=ϵM⇓ϵW
  ϵW≡tt : erase W ≡ $ tt of low
  ϵW≡tt  = proj₁ (⇓ₑ-assign-●-inv ●:=ϵM⇓ϵW)
  ϵM⇓V′ = proj₂ (proj₂ (⇓ₑ-assign-●-inv ●:=ϵM⇓ϵW))
  ϵL:=ϵM⇓tt : erase-μ μ ∣ pc ⊢ erase L := erase M ⇓ₑ $ tt of low ∣ erase-μ μ′
  ϵL:=ϵM⇓tt = ⇓ₑ-assign-● (subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym eq) ϵL⇓ϵV) ϵM⇓V′
  ϵL:=ϵM⇓ϵW : erase-μ μ ∣ pc ⊢ erase L := erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵL:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym ϵW≡tt) ϵL:=ϵM⇓tt
... | ⟨ _ , eq {- a[ low ] n of low ≡ ϵV -} , ϵ-ref-addr {n} ⟩ = ϵL:=ϵM⇓ϵW
  where
  ϵL⇓ϵV : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ erase V ∣ erase-μ μ₁
  ϵL⇓ϵV = sim ⊢L ⊢μ pc≾gc L⇓V⟨c⟩
  ϵelim⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase (elim-ref-proxy V M i _:=_) ⇓ₑ erase W ∣ erase-μ μ′
  ϵelim⇓ϵW =
    case ⇓-value L⇓V⟨c⟩ of λ where
    (V-cast v _) →
      sim (elim-ref-proxy-wt (⊢assign ⊢V⟨c⟩ (relax-Σ ⊢M Σ₁⊇Σ) pc′≼ℓ) v i static) ⊢μ₁ pc≾gc elim⇓W
  ϵV:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ erase V := erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵV:=ϵM⇓ϵW rewrite sym (elim-ref-proxy-erase V M i static refl (error-not-⇓ elim⇓W)) =
    ϵelim⇓ϵW
  a:=ϵM⇓ϵW : erase-μ μ₁ ∣ pc ⊢ (addr a[ low ] n of low) := erase M ⇓ₑ erase W ∣ erase-μ μ′
  a:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ □ := _ ⇓ₑ _ ∣ _) (sym eq) ϵV:=ϵM⇓ϵW
  ϵW≡tt : erase W ≡ $ tt of low
  ϵW≡tt = proj₁ (⇓ₑ-assign-inv a:=ϵM⇓ϵW)
  ϵM⇓V′   = let ⟨ _ , W , w , μ″ , M⇓W , _ ⟩ = ⇓ₑ-assign-inv a:=ϵM⇓ϵW in M⇓W
  ϵμ′≡a∷μ″ = let ⟨ _ , W , w , μ″ , _ , μ′≡a∷μ″ ⟩ = ⇓ₑ-assign-inv a:=ϵM⇓ϵW in μ′≡a∷μ″
  ϵL:=ϵM⇓tt : erase-μ μ ∣ pc ⊢ erase L := erase M ⇓ₑ $ tt of low ∣ erase-μ μ′
  ϵL:=ϵM⇓tt rewrite ϵμ′≡a∷μ″ = ⇓ₑ-assign (subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym eq) ϵL⇓ϵV) ϵM⇓V′
  ϵL:=ϵM⇓ϵW : erase-μ μ ∣ pc ⊢ erase L := erase M ⇓ₑ erase W ∣ erase-μ μ′
  ϵL:=ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym ϵW≡tt) ϵL:=ϵM⇓tt
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢deref ⊢M) ⊢μ pc≾gc
    (⇓-deref-cast {μ₁ = μ₁} {M = M} {V} {W} i M⇓V⟨c⟩ !V⟨oc⟩⇓W)
  with ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V⟨c⟩ , ⊢μ₁ ⟩
  with canonical-ref-erase ⊢V⟨c⟩ (⇓-value M⇓V⟨c⟩)
... | ⟨ _ , eq {- ● ≡ ϵV -} , ϵ-ref-● ⟩ = !ϵM⇓ϵW
  where
  ϵM⇓● : erase-μ μ ∣ pc ⊢ erase M ⇓ₑ ● ∣ erase-μ μ₁
  ϵM⇓● = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym eq) (sim ⊢M ⊢μ pc≾gc M⇓V⟨c⟩)
  !ϵV⇓ϵW : erase-μ μ₁ ∣ pc ⊢ ! (erase V) ⇓ₑ erase W ∣ erase-μ μ′
  !ϵV⇓ϵW =
    case canonical-ref ⊢V⟨c⟩ (⇓-value M⇓V⟨c⟩) of λ where
    (Ref-proxy ref i sub) → sim (⊢cast (⊢deref (ref-wt ref))) ⊢μ₁ pc≾gc !V⟨oc⟩⇓W
  !●⇓ϵW : erase-μ μ₁ ∣ pc ⊢ ! ● ⇓ₑ erase W ∣ erase-μ μ′
  !●⇓ϵW = subst (λ □ → _ ∣ _ ⊢ ! □ ⇓ₑ _ ∣ _) (sym eq) !ϵV⇓ϵW
  ϵW≡● : erase W ≡ ●
  ϵW≡●  = proj₁ (⇓ₑ-deref-●-inv !●⇓ϵW)
  ϵμ₁≡ϵμ′ : erase-μ μ₁ ≡ erase-μ μ′
  ϵμ₁≡ϵμ′ = proj₂ (⇓ₑ-deref-●-inv !●⇓ϵW)
  !ϵM⇓● : erase-μ μ ∣ pc ⊢ ! (erase M) ⇓ₑ ● ∣ erase-μ μ′
  !ϵM⇓● rewrite sym ϵμ₁≡ϵμ′ = ⇓ₑ-deref-● ϵM⇓●
  !ϵM⇓ϵW : erase-μ μ ∣ pc ⊢ ! (erase M) ⇓ₑ erase W ∣ erase-μ μ′
  !ϵM⇓ϵW = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym ϵW≡●) !ϵM⇓●
... | ⟨ _ , eq {- a ≡ ϵV -} , ϵ-ref-addr {n} ⟩ = !ϵM⇓ϵW
  where
  w = ⇓-value !V⟨oc⟩⇓W
  ϵM⇓a : erase-μ μ ∣ pc ⊢ erase M ⇓ₑ addr a[ low ] n of low ∣ erase-μ μ₁
  ϵM⇓a = subst (λ □ → _ ∣ _ ⊢ _ ⇓ₑ □ ∣ _) (sym eq) (sim ⊢M ⊢μ pc≾gc M⇓V⟨c⟩)
  !ϵV⇓ϵW : erase-μ μ₁ ∣ pc ⊢ ! (erase V) ⇓ₑ erase W ∣ erase-μ μ′
  !ϵV⇓ϵW =
    case canonical-ref ⊢V⟨c⟩ (⇓-value M⇓V⟨c⟩) of λ where
    (Ref-proxy ref i sub) → sim (⊢cast (⊢deref (ref-wt ref))) ⊢μ₁ pc≾gc !V⟨oc⟩⇓W
  !a⇓ϵW : erase-μ μ₁ ∣ pc ⊢ ! (addr a[ low ] n of low) ⇓ₑ erase W ∣ erase-μ μ′
  !a⇓ϵW = subst (λ □ → _ ∣ _ ⊢ ! □ ⇓ₑ _ ∣ _) (sym eq) !ϵV⇓ϵW
  hit = let ⟨ _ , eq ⟩ = proj₁ (⇓ₑ-deref-inv !a⇓ϵW) in eq
  ϵμ₁≡ϵμ′ = proj₂ (⇓ₑ-deref-inv !a⇓ϵW)
  !ϵM⇓ϵW : erase-μ μ ∣ pc ⊢ ! (erase M) ⇓ₑ erase W ∣ erase-μ μ′
  !ϵM⇓ϵW rewrite sym ϵμ₁≡ϵμ′ = ⇓ₑ-deref {v = erase-val-value w} ϵM⇓a hit
sim (⊢sub ⊢M A<:B) ⊢μ pc≾gc M⇓V = sim ⊢M ⊢μ pc≾gc M⇓V
sim (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M⇓V = sim ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M⇓V

