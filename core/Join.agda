{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.PathOver

module core.Join where

  postulate

    _*_ : ∀ {ℓ₀ ℓ₁} (X : Set ℓ₀) (Y : Set ℓ₁)
      → Set (ℓ-max ℓ₀ ℓ₁)
    
    jinl : ∀ {ℓ₀ ℓ₁} {X : Set ℓ₀} {Y : Set ℓ₁}
      → X → X * Y
      
    jinr : ∀ {ℓ₀ ℓ₁} {X : Set ℓ₀} {Y : Set ℓ₁}
      → Y → X * Y
      
    jglue : ∀ {ℓ₀ ℓ₁} {X : Set ℓ₀} {Y : Set ℓ₁}
      → (x : X) (y : Y)
      → jinl x ≡ jinr y

    Join-elim : ∀ {ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ₀} {Y : Set ℓ₁}
      → {P : X * Y → Set ℓ₂}
      → (jinl* : (x : X) → P (jinl x))
      → (jinr* : (y : Y) → P (jinr y))
      → (jglue* : (x : X) (y : Y) → jinl* x ≡ jinr* y [ P ↓ jglue x y ]) 
      → (xy : X * Y) → P xy 
    
    Join-elim-jinl-β : ∀ {ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ₀} {Y : Set ℓ₁}
      → {P : X * Y → Set ℓ₂}
      → (jinl* : (x : X) → P (jinl x))
      → (jinr* : (y : Y) → P (jinr y))
      → (jglue* : (x : X) (y : Y) → jinl* x ≡ jinr* y [ P ↓ jglue x y ]) 
      → (x : X)
      → Join-elim {P = P} jinl* jinr* jglue* (jinl x) ↦ jinl* x
    {-# REWRITE Join-elim-jinl-β #-}

    Join-elim-jinr-β : ∀ {ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ₀} {Y : Set ℓ₁}
      → {P : X * Y → Set ℓ₂}
      → (jinl* : (x : X) → P (jinl x))
      → (jinr* : (y : Y) → P (jinr y))
      → (jglue* : (x : X) (y : Y) → jinl* x ≡ jinr* y [ P ↓ jglue x y ]) 
      → (y : Y)
      → Join-elim {P = P} jinl* jinr* jglue* (jinr y) ↦ jinr* y
    {-# REWRITE Join-elim-jinr-β #-}

    Join-elim-jglue-β : ∀ {ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ₀} {Y : Set ℓ₁}
      → {P : X * Y → Set ℓ₂}
      → (jinl* : (x : X) → P (jinl x))
      → (jinr* : (y : Y) → P (jinr y))
      → (jglue* : (x : X) (y : Y) → jinl* x ≡ jinr* y [ P ↓ jglue x y ]) 
      → (x : X) (y : Y)
      → apd (Join-elim {P = P} jinl* jinr* jglue*) (jglue x y) ↦ jglue* x y
    {-# REWRITE Join-elim-jglue-β #-} 
