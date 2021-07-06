{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.Path
open import core.Coproduct

module core.Decidable where

  Dec : ∀ {ℓ} → Set ℓ → Set ℓ
  Dec X = X ⊔ ¬ X 

  
