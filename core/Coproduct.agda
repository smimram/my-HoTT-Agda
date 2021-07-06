{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.Path

module core.Coproduct where

  data _⊔_ {ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ-max ℓ₀ ℓ₁) where
    inl : A → A ⊔ B
    inr : B → A ⊔ B 

