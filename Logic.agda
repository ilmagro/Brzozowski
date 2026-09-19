{-# OPTIONS --cubical-compatible --safe #-}

open import Agda.Primitive

module Logic where

open import Agda.Builtin.Sigma public

record ⊤ {𝑎} : Set 𝑎 where
  instance constructor tt

data ⊥ {𝑎} : Set 𝑎 where

⊥-elim : ∀ {𝑎 𝑝} {A : Set 𝑎} → ⊥ {𝑝} → A
⊥-elim ()

¬_ : ∀ {𝑎} → Set 𝑎 → Set 𝑎
¬_ {𝑎} A = A → ⊥ {𝑎}

data _⊎_ {𝑎 𝑏} (A : Set 𝑎) (B : Set 𝑏) : Set (𝑎 ⊔ 𝑏) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

⊎-elim : ∀ {𝑎 𝑏 𝑐} {A : Set 𝑎} {B : Set 𝑏} {C : Set 𝑐} → (A → C) → (B → C) → A ⊎ B → C
⊎-elim p _ (inl a) = p a
⊎-elim _ q (inr b) = q b

_×_ : ∀ {𝑎 𝑏} (A : Set 𝑎) (B : Set 𝑏) → Set (𝑎 ⊔ 𝑏)
A × B = Σ A λ _ → B
infixl 3 _×_
