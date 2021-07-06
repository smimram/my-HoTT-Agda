{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.NType
open import core.Truncation
open import core.Equivalence

module core.FinType where

  data Fin : ℕ → Set where 
    O : {n : ℕ} → Fin (S n)
    S : {n : ℕ} → Fin n → Fin (S n)

  is-finite : ∀ {ℓ} → Set ℓ → Set ℓ
  is-finite X = Σ ℕ (λ n → Trunc ⟨-1⟩ (X ≃ Fin n))

  FinType : ∀ {ℓ} → Set (ℓ-suc ℓ)
  FinType {ℓ} = Σ (Set ℓ) is-finite
