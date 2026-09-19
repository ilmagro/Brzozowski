{-# OPTIONS --cubical-compatible --safe #-}

module List.Base where

open import Agda.Builtin.List public

_++_ : ∀ {𝑎} {A : Set 𝑎} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

foldl : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} → (B → A → B) → B → List A → B
foldl f b []       = b
foldl f b (x ∷ xs) = foldl f (f b x) xs
