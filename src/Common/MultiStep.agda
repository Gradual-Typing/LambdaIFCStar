module Common.MultiStep (A : Set) (B : (x y : A) → Set) (_—→_ : ∀ {x y} → (M N : B x y) → Set) where


infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {x y : A} (M N : B x y) → Set where
  _∎ : ∀ {x y} (M : B x y)
      ---------------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {x y} (L : B x y) {M N}
    → L —→ M
    → M —↠ N
      ---------------
    → L —↠ N


↠-trans : ∀ {x y} {L M N : B x y}
  → L —↠ M
  → M —↠ N
  → L —↠ N
↠-trans (L ∎) (._ ∎) = L ∎
↠-trans (L ∎) (.L —→⟨ M→ ⟩ ↠N) = L —→⟨ M→ ⟩ ↠N
↠-trans (L —→⟨ L→ ⟩ ↠M) (M ∎) = L —→⟨ L→ ⟩ ↠M
↠-trans (L —→⟨ L→ ⟩ ↠M) (M —→⟨ M→ ⟩ ↠N) = L —→⟨ L→ ⟩ ↠-trans ↠M (M —→⟨ M→ ⟩ ↠N)
