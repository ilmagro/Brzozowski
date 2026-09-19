{-# OPTIONS --cubical-compatible --safe #-}

module Ensemble where

Ensemble : ∀ {𝑎} → Set 𝑎 → (ℓ : _) → Set _
Ensemble A ℓ = A → Set ℓ

_∈_ : ∀ {𝑎 ℓ} {A : Set 𝑎} → A → (A → Set ℓ) → Set ℓ
_∈_ x P = P x
infix 21 _∈_
