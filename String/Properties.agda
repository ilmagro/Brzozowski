{-# OPTIONS --cubical-compatible --safe #-}

open import Agda.Builtin.Nat
open import Ensemble
open import Equality
open import List.Base
open import List.Properties
open import Logic

module String.Properties {𝑎} (A : Set 𝑎) where

open import String.Base A

^-++-closure : ∀ {𝑆 xs ys n} m → xs ∈ (𝑆 ^ m) → ys ∈ (𝑆 ^ n) → (xs ++ ys) ∈ (𝑆 ^ (m + n))
^-++-closure zero    refl                    p = p
^-++-closure (suc m) (vs , ws , (p , q) , r) s = vs , (ws ++ _) ,
                                                 (trans (cong (_++ _) p) (++-assoc vs ws _) , q) ,
                                                 ^-++-closure m r s

⋆-++-closure : ∀ {𝑆 ys zs} → ys ∈ (𝑆 ⋆) → zs ∈ (𝑆 ⋆) → (ys ++ zs) ∈ (𝑆 ⋆)
⋆-++-closure (m , p) (n , q) = m + n , ^-++-closure m p q

⋆-idem-left : ∀ {𝑆 xs} → xs ∈ ((𝑆 ⋆) ⋆) → xs ∈ (𝑆 ⋆)
⋆-idem-left     (zero , p)                      = zero , p
⋆-idem-left {𝑆} (suc n , ys , zs , (q , r) , t) = subst (_∈ (𝑆 ⋆))
                                                  (sym q)
                                                  (⋆-++-closure r (⋆-idem-left (n , t)))

⋆-idem-right : ∀ {𝑆 xs} → xs ∈ (𝑆 ⋆) → xs ∈ ((𝑆 ⋆) ⋆)
⋆-idem-right p = 1 , _ , [] , ((sym (++-[]-id-right _) , p) , refl)
