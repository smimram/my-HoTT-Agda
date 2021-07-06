{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.Path

module core.NType where

  is-contr : ∀ {ℓ} → Set ℓ → Set ℓ
  is-contr X = Σ X (λ x → (y : X) → x ≡ y)

  data ℕ₋₂ : Set where
    ⟨-2⟩ : ℕ₋₂
    ⟨S⟩ : ℕ₋₂ → ℕ₋₂

  ⟨-1⟩ : ℕ₋₂
  ⟨-1⟩ = ⟨S⟩ ⟨-2⟩

  ⟨0⟩ : ℕ₋₂
  ⟨0⟩ = ⟨S⟩ ⟨-1⟩ 

  is-ntype : ∀ {ℓ} (n : ℕ₋₂) → Set ℓ → Set ℓ
  is-ntype ⟨-2⟩ X = is-contr X
  is-ntype (⟨S⟩ n) X =
    (x y : X) → is-ntype n (x ≡ y)

  contr-has-all-paths : ∀ {ℓ} {X : Set ℓ}
    → is-contr X → (x y : X) → x ≡ y
  contr-has-all-paths (ctr , ϕ) x y = ! (ϕ x) ∙ ϕ y 

  hom-is-contr : ∀ {ℓ} {X : Set ℓ}
    → (c : is-contr X)
    → (x y : X) → is-contr (x ≡ y)
  hom-is-contr (ctr , ϕ) x y =
    contr-has-all-paths (ctr , ϕ) x y , lem 

    where lem : (p : x ≡ y) → ! (ϕ x) ∙ ϕ y ≡  p
          lem refl = ∙-inv-l (ϕ x) 
  
  is-prop : ∀ {ℓ} → Set ℓ → Set ℓ
  is-prop = is-ntype ⟨-1⟩ 

  is-set : ∀ {ℓ} → Set ℓ → Set ℓ
  is-set = is-ntype ⟨0⟩

  
