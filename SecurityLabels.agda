module SecurityLabels where

open import Data.Maybe
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Utils


{- **** Security labels **** -}
data StaticLabel : Set where
  high : StaticLabel
  low  : StaticLabel

data Label : Set where
  ⋆ : Label
  l : StaticLabel → Label

_=?_ : ∀ (ℓ₁ ℓ₂ : StaticLabel) → Dec (ℓ₁ ≡ ℓ₂)
low  =? low  = yes refl
high =? high = yes refl
low  =? high = no λ ()
high =? low  = no λ ()


{- **** Label partial order **** -}
infix 5 _≼_

data _≼_ : StaticLabel → StaticLabel → Set where
  l≼l : low  ≼ low
  l≼h : low  ≼ high
  h≼h : high ≼ high

low≼ : ∀ ℓ → low ≼ ℓ
low≼ low  = l≼l
low≼ high = l≼h

_≼high : ∀ ℓ → ℓ ≼ high
low  ≼high = l≼h
high ≼high = h≼h

≼-refl : ∀ {ℓ} → ℓ ≼ ℓ
≼-refl {high}  = h≼h
≼-refl {low}   = l≼l

≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃}
  → ℓ₁ ≼ ℓ₂ → ℓ₂ ≼ ℓ₃ → ℓ₁ ≼ ℓ₃
≼-trans l≼l l≼l = l≼l
≼-trans l≼l l≼h = l≼h
≼-trans l≼h h≼h = l≼h
≼-trans h≼h h≼h = h≼h

≼-antisym : ∀ {ℓ₁ ℓ₂}
  → ℓ₁ ≼ ℓ₂ → ℓ₂ ≼ ℓ₁ → ℓ₁ ≡ ℓ₂
≼-antisym l≼l l≼l = refl
≼-antisym h≼h h≼h = refl

infix 4 _≼?_

_≼?_ : ∀ ℓ₁ ℓ₂ → Dec (ℓ₁ ≼ ℓ₂)
low  ≼? low  = yes l≼l
low  ≼? high = yes l≼h
high ≼? high = yes h≼h
high ≼? low  = no λ ()


{- **** Label subtyping **** -}
infix 5 _<:ₗ_

data _<:ₗ_ : Label → Label → Set where
  <:-⋆ : ⋆ <:ₗ ⋆      {- ⋆ is neutral -}
  <:-l : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≼ ℓ₂ → l ℓ₁ <:ₗ l ℓ₂

<:ₗ-refl : ∀ {g} → g <:ₗ g
<:ₗ-refl {⋆}   = <:-⋆
<:ₗ-refl {l ℓ} = <:-l ≼-refl

<:ₗ-trans : ∀ {g₁ g₂ g₃} → g₁ <:ₗ g₂ → g₂ <:ₗ g₃ → g₁ <:ₗ g₃
<:ₗ-trans <:-⋆ <:-⋆ = <:-⋆
<:ₗ-trans (<:-l ℓ₁≼ℓ₂) (<:-l ℓ₂≼ℓ₃) = <:-l (≼-trans ℓ₁≼ℓ₂ ℓ₂≼ℓ₃)

<:ₗ-antisym : ∀ {g₁ g₂}
  → g₁ <:ₗ g₂ → g₂ <:ₗ g₁ → g₁ ≡ g₂
<:ₗ-antisym <:-⋆ <:-⋆ = refl
<:ₗ-antisym (<:-l ℓ₁≼ℓ₂) (<:-l ℓ₂≼ℓ₁) = cong l (≼-antisym ℓ₁≼ℓ₂ ℓ₂≼ℓ₁)


{- **** Label consistency **** -}
infix 5 _~ₗ_

data _~ₗ_ : Label → Label → Set where
  ⋆~ : ∀ {g} → ⋆ ~ₗ g
  ~⋆ : ∀ {g} → g ~ₗ ⋆
  l~ : ∀ {ℓ} → l ℓ ~ₗ l ℓ

~ₗ-refl : ∀ {g} → g ~ₗ g
~ₗ-refl {⋆}   = ⋆~
~ₗ-refl {l _} = l~

~ₗ-sym : ∀ {g₁ g₂} → g₁ ~ₗ g₂ → g₂ ~ₗ g₁
~ₗ-sym ⋆~ = ~⋆
~ₗ-sym ~⋆ = ⋆~
~ₗ-sym l~ = l~


{- **** Label consistent subtyping **** -}
infix 5 _≾_

data _≾_ : Label → Label → Set where
  ≾-⋆r : ∀ {g}     → g ≾ ⋆
  ≾-⋆l : ∀ {g}     → ⋆ ≾ g
  ≾-l  : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≼ ℓ₂ → l ℓ₁ ≾ l ℓ₂

low≾ : ∀ g → l low ≾ g
low≾ ⋆ = ≾-⋆r
low≾ (l ℓ) = ≾-l (low≼ ℓ)

_≾high : ∀ g → g ≾ l high
⋆ ≾high = ≾-⋆l
(l ℓ) ≾high = ≾-l (ℓ ≼high)

≾-refl : ∀ {g} → g ≾ g
≾-refl {⋆}   = ≾-⋆r
≾-refl {l x} = ≾-l ≼-refl

≾-antisym : ∀ {g₁ g₂}
  → g₁ ≾ g₂ → g₂ ≾ g₁ → g₁ ~ₗ g₂
≾-antisym ≾-⋆r _ = ~⋆
≾-antisym ≾-⋆l _ = ⋆~
≾-antisym (≾-l ℓ₁≼ℓ₂) (≾-l ℓ₂≼ℓ₂)
  rewrite ≼-antisym ℓ₁≼ℓ₂ ℓ₂≼ℓ₂ = ~ₗ-refl

-- Properties of label consistent subtyping
≾-prop : ∀ {g₁ g₂ : Label}
  → g₁ ≾ g₂
  → ∃[ g ] (g₁ ~ₗ g) × (g <:ₗ g₂)
≾-prop {g} {⋆} ≾-⋆r = ⟨ ⋆ , ~⋆ , <:-⋆ ⟩
≾-prop {⋆} {g} ≾-⋆l = ⟨ g , ⋆~ , <:ₗ-refl ⟩
≾-prop {l ℓ₁} {l ℓ₂} (≾-l ℓ₁≼ℓ₂) =
  ⟨ l ℓ₁ , ~ₗ-refl , <:-l ℓ₁≼ℓ₂ ⟩

≾-prop′ : ∀ {g₁ g₂ : Label}
  → g₁ ≾ g₂
  → ∃[ g ] (g₁ <:ₗ g) × (g ~ₗ g₂)
≾-prop′ {g} {⋆} ≾-⋆r = ⟨ g , <:ₗ-refl , ~⋆ ⟩
≾-prop′ {⋆} {g} ≾-⋆l = ⟨ ⋆ , <:-⋆ , ⋆~ ⟩
≾-prop′ {l ℓ₁} {l ℓ₂} (≾-l ℓ₁≼ℓ₂) =
  ⟨ l ℓ₂ , <:-l ℓ₁≼ℓ₂ , ~ₗ-refl ⟩

-- Consistency implies consistent subtyping
~ₗ→≾ : ∀ {g₁ g₂} → g₁ ~ₗ g₂ → g₁ ≾ g₂ × g₂ ≾ g₁
~ₗ→≾ ⋆~ = ⟨ ≾-⋆l , ≾-⋆r ⟩
~ₗ→≾ ~⋆ = ⟨ ≾-⋆r , ≾-⋆l ⟩
~ₗ→≾ (l~ {low}) = ⟨ ≾-l l≼l , ≾-l l≼l ⟩
~ₗ→≾ (l~ {high}) = ⟨ ≾-l h≼h , ≾-l h≼h ⟩


{- **** Label join **** -}
_⋎_ : StaticLabel → StaticLabel → StaticLabel
low ⋎ low = low
_   ⋎ _   = high

{- **** Label meet **** -}
_⋏_ : StaticLabel → StaticLabel → StaticLabel
high ⋏ high = high
_    ⋏ _    = low

⋎-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃} → (ℓ₁ ⋎ ℓ₂) ⋎ ℓ₃ ≡ ℓ₁ ⋎ (ℓ₂ ⋎ ℓ₃)
⋎-assoc {high} = refl
⋎-assoc {low} {high} = refl
⋎-assoc {low} {low} {high} = refl
⋎-assoc {low} {low} {low} = refl

ℓ⋎ℓ≡ℓ : ∀ {ℓ} → ℓ ⋎ ℓ ≡ ℓ
ℓ⋎ℓ≡ℓ {high} = refl
ℓ⋎ℓ≡ℓ {low} = refl

ℓ₁⋎[ℓ₁⋎ℓ]≡ℓ₁⋎ℓ : ∀ {ℓ ℓ₁} → ℓ₁ ⋎ (ℓ₁ ⋎ ℓ) ≡ ℓ₁ ⋎ ℓ
ℓ₁⋎[ℓ₁⋎ℓ]≡ℓ₁⋎ℓ {ℓ} {ℓ₁}
  rewrite sym (⋎-assoc {ℓ₁} {ℓ₁} {ℓ})
  rewrite (ℓ⋎ℓ≡ℓ {ℓ₁}) = refl

ℓ⋎high≡high : ∀ {ℓ} → ℓ ⋎ high ≡ high
ℓ⋎high≡high {low}  = refl
ℓ⋎high≡high {high} = refl

ℓ⋎low≡ℓ : ∀ {ℓ} → ℓ ⋎ low ≡ ℓ
ℓ⋎low≡ℓ {low}  = refl
ℓ⋎low≡ℓ {high} = refl

-- TODO: better names
join-≼ : ∀ {ℓ₁ ℓ₂ ℓ}
  → ℓ₁ ⋎ ℓ₂ ≼ ℓ
  → ℓ₁ ≼ ℓ × ℓ₂ ≼ ℓ
join-≼ {high} {high} {high} _ = ⟨ h≼h , h≼h ⟩
join-≼ {high} {low} {high} _ = ⟨ h≼h , l≼h ⟩
join-≼ {low} {high} {high} _ = ⟨ l≼h , h≼h ⟩
join-≼ {low} {low} {high} _ = ⟨ l≼h , l≼h ⟩
join-≼ {low} {low} {low} _ = ⟨ l≼l , l≼l ⟩

meet-≼ : ∀ {ℓ₁ ℓ₂ ℓ}
  → ℓ ≼ ℓ₁ ⋏ ℓ₂
  → ℓ ≼ ℓ₁ × ℓ ≼ ℓ₂
meet-≼ {high} {high} {high} _ = ⟨ h≼h , h≼h ⟩
meet-≼ {high} {high} {low} _ = ⟨ l≼h , l≼h ⟩
meet-≼ {high} {low} {low} _ = ⟨ l≼h , l≼l ⟩
meet-≼ {low} {high} {low} _ = ⟨ l≼l , l≼h ⟩
meet-≼ {low} {low} {low} _ = ⟨ l≼l , l≼l ⟩

join-≼′ : ∀ {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′}
  → ℓ₁ ≼ ℓ₁′ → ℓ₂ ≼ ℓ₂′ → (ℓ₁ ⋎ ℓ₂) ≼ (ℓ₁′ ⋎ ℓ₂′)
join-≼′ l≼l l≼l = l≼l
join-≼′ l≼l l≼h = l≼h
join-≼′ l≼l h≼h = h≼h
join-≼′ l≼h l≼l = l≼h
join-≼′ l≼h l≼h = l≼h
join-≼′ l≼h h≼h = h≼h
join-≼′ h≼h _ = h≼h


{- **** Label consistent join **** -}
_⋎̃_ : Label → Label → Label
l ℓ₁     ⋎̃ l ℓ₂   = l (ℓ₁ ⋎ ℓ₂)
-- l high   ⋎̃ ⋆      = l high
_        ⋎̃ ⋆      = ⋆
-- ⋆        ⋎̃ l high = l high
⋆        ⋎̃ _      = ⋆

{- **** Label consistent meet **** -}
_⋏̃_ : Label → Label → Label
l ℓ₁     ⋏̃ l ℓ₂   = l (ℓ₁ ⋏ ℓ₂)
-- l low    ⋏̃ ⋆      = l low
_        ⋏̃ ⋆      = ⋆
-- ⋆        ⋏̃ l low  = l low
⋆        ⋏̃ _      = ⋆

g⋎̃g≡g : ∀ {g} → g ⋎̃ g ≡ g
g⋎̃g≡g {⋆} = refl
g⋎̃g≡g {l ℓ} = cong l ℓ⋎ℓ≡ℓ

g⋎̃⋆≡⋆ : ∀ {g} → g ⋎̃ ⋆ ≡ ⋆
g⋎̃⋆≡⋆ {⋆} = refl
g⋎̃⋆≡⋆ {l ℓ} = refl

g⋎̃low≡g : ∀ {g} → g ⋎̃ l low ≡ g
g⋎̃low≡g {⋆} = refl
g⋎̃low≡g {l ℓ} = cong l ℓ⋎low≡ℓ

consis-join-~ₗ : ∀ {g₁ g₂ g₃ g₄} → g₁ ~ₗ g₂ → g₃ ~ₗ g₄ → g₁ ⋎̃ g₃ ~ₗ g₂ ⋎̃ g₄
consis-join-~ₗ {g₃ = ⋆} ⋆~ _ = ⋆~
consis-join-~ₗ {g₃ = l _} ⋆~ _ = ⋆~
consis-join-~ₗ {g₄ = ⋆} ~⋆ _ = ~⋆
consis-join-~ₗ {g₄ = l _} ~⋆ _ = ~⋆
consis-join-~ₗ l~ ⋆~ = ⋆~
consis-join-~ₗ l~ ~⋆ = ~⋆
consis-join-~ₗ l~ l~ = l~

consis-join-≾ : ∀ {g₁ g₂ g₃ g₄} → g₁ ≾ g₃ → g₂ ≾ g₄ → g₁ ⋎̃ g₂ ≾ g₃ ⋎̃ g₄
consis-join-≾ {g₄ = ⋆} ≾-⋆r y = ≾-⋆r
consis-join-≾ {g₄ = l _} ≾-⋆r y = ≾-⋆r
consis-join-≾ {g₂ = ⋆} ≾-⋆l y = ≾-⋆l
consis-join-≾ {g₂ = l _} ≾-⋆l y = ≾-⋆l
consis-join-≾ (≾-l _) ≾-⋆r = ≾-⋆r
consis-join-≾ (≾-l _) ≾-⋆l = ≾-⋆l
consis-join-≾ (≾-l ℓ₁≼ℓ₃) (≾-l ℓ₂≼ℓ₄) = ≾-l (join-≼′ ℓ₁≼ℓ₃ ℓ₂≼ℓ₄)

consis-join-≾-inv : ∀ {g₁ g₂ g} → g₁ ⋎̃ g₂ ≡ g → g₁ ≾ g × g₂ ≾ g
consis-join-≾-inv {g = ⋆} eq = ⟨ ≾-⋆r , ≾-⋆r ⟩
consis-join-≾-inv {l ℓ₁} {l ℓ₂} {l ℓ} refl =
  case join-≼ {ℓ₁} {ℓ₂} {ℓ} ≼-refl of λ where
    ⟨ ℓ₁≼ℓ₁⋎ℓ₂ , ℓ₂≼ℓ₁⋎ℓ₂ ⟩ → ⟨ ≾-l ℓ₁≼ℓ₁⋎ℓ₂ , ≾-l ℓ₂≼ℓ₁⋎ℓ₂ ⟩
consis-join-≾-inv {⋆} {l ℓ₂} {l ℓ} ()

consis-meet-≾-inv : ∀ {g₁ g₂ g} → g ≡ g₁ ⋏̃ g₂ → g ≾ g₁ × g ≾ g₂
consis-meet-≾-inv {g = ⋆} eq = ⟨ ≾-⋆l , ≾-⋆l ⟩
consis-meet-≾-inv {l ℓ₁} {l ℓ₂} {l ℓ} refl =
  case meet-≼ {ℓ₁} {ℓ₂} {ℓ} ≼-refl of λ where
    ⟨ ℓ₁⋏ℓ₂≼ℓ₁ , ℓ₁⋏ℓ₂≼ℓ₂ ⟩ → ⟨ ≾-l ℓ₁⋏ℓ₂≼ℓ₁ , ≾-l ℓ₁⋏ℓ₂≼ℓ₂ ⟩
consis-meet-≾-inv {l ℓ₁} {⋆} {l ℓ} ()

consis-join-<:ₗ : ∀ {g₁ g₁′ g₂ g₂′} → g₁ <:ₗ g₁′ → g₂ <:ₗ g₂′ → g₁ ⋎̃ g₂ <:ₗ g₁′ ⋎̃ g₂′
consis-join-<:ₗ <:-⋆ <:-⋆ = <:-⋆
consis-join-<:ₗ <:-⋆ (<:-l x) = <:-⋆
consis-join-<:ₗ (<:-l x) <:-⋆ = <:-⋆
consis-join-<:ₗ (<:-l ℓ₁≼ℓ₁′) (<:-l ℓ₂≼ℓ₂′) = <:-l (join-≼′ ℓ₁≼ℓ₁′ ℓ₂≼ℓ₂′)

consis-join-<:ₗ-inv : ∀ {g₁ g₂ ℓ} → g₁ ⋎̃ g₂ <:ₗ l ℓ → (g₁ <:ₗ l ℓ) × (g₂ <:ₗ l ℓ)
consis-join-<:ₗ-inv {⋆} {⋆} ()
consis-join-<:ₗ-inv {l ℓ₁} {l ℓ₂} (<:-l ℓ₁⋎ℓ₂≼ℓ) =
  let ⟨ ℓ₁≼ℓ , ℓ₂≼ℓ ⟩ = join-≼ ℓ₁⋎ℓ₂≼ℓ in ⟨ <:-l ℓ₁≼ℓ , <:-l ℓ₂≼ℓ ⟩

≾-<: : ∀ {g₁ g₂ g} → g₁ ≾ g₂ → g₂ <:ₗ g → g₁ ≾ g
≾-<: {g₂ = ⋆} g₁≾g₂ <:-⋆ = ≾-⋆r
≾-<: {⋆} {l ℓ₂} g₁≾g₂ g₂<:g = ≾-⋆l
≾-<: {l ℓ₁} {l ℓ₂} {l ℓ} (≾-l ℓ₁≼ℓ₂) (<:-l ℓ₂≼ℓ) = ≾-l (≼-trans ℓ₁≼ℓ₂ ℓ₂≼ℓ)


{- **** Label precision join **** -}
⨆ₗ : ∀ {g₁ g₂} → g₁ ~ₗ g₂ → Label -- of labels

⨆ₗ {⋆} {g}     ⋆~ = g
⨆ₗ {g} {⋆}     ~⋆ = g
⨆ₗ {l ℓ} {l ℓ} l~ = l ℓ


{- **** Label gradual meet **** -}
infix 5 _⊓ₗ_

_⊓ₗ_ : Label → Label → Maybe Label
l high ⊓ₗ l high = just (l high)
l low  ⊓ₗ l low  = just (l low)
⋆      ⊓ₗ g      = just g
g      ⊓ₗ ⋆      = just g
_      ⊓ₗ _      = nothing

grad-meet-~ₗ : ∀ {g₁ g₂ g}
  → g₁ ⊓ₗ g₂ ≡ just g
  → g₁ ~ₗ g × g₂ ~ₗ g
grad-meet-~ₗ {⋆} {⋆} {⋆} refl = ⟨ ⋆~ , ⋆~ ⟩
grad-meet-~ₗ {⋆} {l low} {l low} refl = ⟨ ⋆~ , l~ ⟩
grad-meet-~ₗ {⋆} {l high} {l high} refl = ⟨ ⋆~ , l~ ⟩
grad-meet-~ₗ {l high} {⋆} {l high} refl = ⟨ l~ , ⋆~ ⟩
grad-meet-~ₗ {l high} {l high} {l high} refl = ⟨ l~ , l~ ⟩
grad-meet-~ₗ {l low} {⋆} {l low} refl = ⟨ l~ , ⋆~ ⟩
grad-meet-~ₗ {l low} {l low} {l low} refl = ⟨ l~ , l~ ⟩
