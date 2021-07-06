{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.NType

module core.Truncation where

  postulate

    Trunc : ∀ {ℓ} (n : ℕ₋₂) (X : Set ℓ) → Set ℓ
    ⟦_⟧ : ∀ {ℓ} {n : ℕ₋₂} {X : Set ℓ}
      → X → Trunc n X 

    Trunc-elim : ∀ {ℓ₀ ℓ₁} {n : ℕ₋₂}
      → {X : Set ℓ₀} {P : Trunc n X → Set ℓ₁} 
      → (is-ntype* : (x : Trunc n X) → is-ntype n (P x))
      → (ρ : (x : X) → P ⟦ x ⟧)
      → (x : Trunc n X) → P x

    Trunc-elim-β : ∀ {ℓ₀ ℓ₁} {n : ℕ₋₂}
      → {X : Set ℓ₀} {P : Trunc n X → Set ℓ₁} 
      → (is-ntype* : (x : Trunc n X) → is-ntype n (P x))
      → (ρ : (x : X) → P ⟦ x ⟧) (x : X)
      → Trunc-elim {P = P} is-ntype* ρ ⟦ x ⟧ ↦ ρ x
    {-# REWRITE Trunc-elim-β #-}

  Trunc-rec : ∀ {ℓ₀ ℓ₁} {n : ℕ₋₂}
    → {X : Set ℓ₀} {A : Set ℓ₁}
    → (is-ntype* : is-ntype n A)
    → (ρ : X → A)
    → Trunc n X → A
  Trunc-rec {X = X} {A} is-ntype* ρ =
    Trunc-elim {X = X} {P = cst A} (cst is-ntype*) ρ 
    
