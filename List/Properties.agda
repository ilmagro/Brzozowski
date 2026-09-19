{-# OPTIONS --cubical-compatible --safe #-}

open import Equality
open import List.Base

module List.Properties where

∷-inj-left : ∀ {𝑎} {A : Set 𝑎} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷-inj-left {A = A} {x} eq = cong (head {x}) eq
  where
  head : {A} → List A → A
  head {x} []      = x
  head     (y ∷ _) = y

∷-inj-right : ∀ {𝑎} {A : Set 𝑎} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-inj-right {A = A} eq = cong tail eq
  where
  tail : List A → List A
  tail []       = []
  tail (_ ∷ xs) = xs

++-[]-cancel-left : ∀ {𝑎} {A : Set 𝑎} {xs ys : List A} → xs ++ ys ≡ [] → xs ≡ []
++-[]-cancel-left {xs = []} _ = refl

++-[]-cancel-right : ∀ {𝑎} {A : Set 𝑎} {xs ys : List A} → xs ++ ys ≡ [] → ys ≡ []
++-[]-cancel-right {xs = []} eq = eq

++-[]-id-right : ∀ {𝑎} {A : Set 𝑎} (xs : List A) → xs ++ [] ≡ xs
++-[]-id-right []       = refl
++-[]-id-right (x ∷ xs) = cong (_ ∷_) (++-[]-id-right xs)

++-assoc : ∀ {𝑎} {A : Set 𝑎} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_ ∷_) (++-assoc xs ys zs)
