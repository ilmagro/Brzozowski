{-# OPTIONS --cubical-compatible --safe #-}

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Equality
open import Ensemble
open import List.Base
open import Logic

module String.Base {𝑎} (A : Set 𝑎) where

String = List A
ε = [] {A = A}

_∙_ : Ensemble String 𝑎 → Ensemble String 𝑎 → Ensemble String _
𝑆 ∙ 𝑇 = λ xs → Σ _ λ ys → Σ _ λ zs → (xs ≡ ys ++ zs) × ys ∈ 𝑆 × zs ∈ 𝑇

_^_ : Ensemble String 𝑎 → ℕ → Ensemble String _
𝑆 ^ zero  = λ xs → xs ≡ ε
𝑆 ^ suc n = 𝑆 ∙ (𝑆 ^ n)

_⋆ : Ensemble String _ → Ensemble String _ 
𝑆 ⋆ = λ xs → Σ _ λ n → xs ∈ (𝑆 ^ n)
