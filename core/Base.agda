{-# OPTIONS --without-K --rewriting #-}

module core.Base where

  open import Agda.Primitive public
    using    ( Level )
    renaming ( lzero to ℓ-zero 
             ; lsuc  to ℓ-suc
             ; _⊔_   to ℓ-max )

  infix 10 _↦_
  postulate  
    _↦_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ

  {-# BUILTIN REWRITE _↦_ #-}

  --
  -- Universes
  --

  Type : ∀ ℓ → Set (ℓ-suc ℓ)
  Type ℓ = Set ℓ

  Type₀ = Set
  Type₁ = Set₁

  record Lift {ℓ₀ ℓ₁} (A : Type ℓ₀) : Set (ℓ-max ℓ₀ ℓ₁) where
    constructor lift
    field lower : A

  --
  -- Dependent Sum
  --
  
  open import Agda.Builtin.Sigma public
  
  infixl 40 _×_
  
  _×_ : ∀ {ℓ₀ ℓ₁} → Set ℓ₀ → Set ℓ₁ → Set (ℓ-max ℓ₀ ℓ₁)
  A × B = Σ A (λ _ → B)

  --
  -- Natural numbers
  --
  
  data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

  --
  -- The Empty type
  --
  
  data ∅ {ℓ} : Set ℓ where

  infix 100 ¬_
  
  ¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
  ¬_ {ℓ} X = X → ∅ {ℓ}

  --
  -- The Unit type
  --
  
  record ⊤ {ℓ} : Set ℓ where
    constructor tt

  {-# BUILTIN UNIT ⊤ #-}

  --
  --  Equality
  --
  
  data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
    refl : a ≡ a

  {-# BUILTIN EQUALITY _≡_ #-}

  _≠_ : ∀ {ℓ} {A : Set ℓ} (a b : A) → Set ℓ
  a ≠ b = ¬ (a ≡ b)

  --
  --  Function primitives
  --

  Π : ∀ {ℓ₀ ℓ₁} (A : Type ℓ₀) (B : A → Type ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
  Π A B = (x : A) → B x

  id : ∀ {ℓ₀} {X : Set ℓ₀} → X → X
  id x = x  

  cst : ∀ {ℓ₀ ℓ₁} {X : Set ℓ₀} {Y : Set ℓ₁}
    → (y : Y) → X → Y
  cst y _ = y

  infixr 20 _∘_
  
  _∘_ : ∀ {ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ₀} {Y : Set ℓ₁} {Z : Set ℓ₂}
    → (f : Y → Z) (g : X → Y) → X → Z
  (f ∘ g) x = f (g x)

  infixr 50 _∼_
  
  _∼_ :  ∀ {ℓ₀ ℓ₁} {A : Set ℓ₀} {B : A → Set ℓ₁}
    → (f g : (x : A) → B x)
    → Set (ℓ-max ℓ₀ ℓ₁)
  _∼_ f g = ∀ x → f x ≡ g x

