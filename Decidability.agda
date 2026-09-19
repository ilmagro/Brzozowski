{-# OPTIONS --cubical-compatible --safe #-}

open import Agda.Primitive
open import Logic

module Decidability where

data Dec {𝑝} (P : Set 𝑝) : Set 𝑝 where
  yes : P → Dec P
  no  : ¬ P → Dec P
