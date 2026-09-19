{-# OPTIONS --cubical-compatible --safe #-}

open import Agda.Builtin.Nat
open import Decidability
open import Ensemble
open import Equality
open import List.Base
open import List.Properties
open import Logic

module Brzozowski {𝑎} (A : Set 𝑎)
                      (_≟_ : ∀ (x y : A) → Dec (x ≡ y)) where

open import String.Base A

data RegExp : Set 𝑎 where
  zeroᴿ : RegExp
  oneᴿ  : RegExp
  varᴿ  : A → RegExp
  _+ᴿ_  : RegExp → RegExp → RegExp
  _*ᴿ_  : RegExp → RegExp → RegExp
  _⋆ᴿ   : RegExp → RegExp

ℒ : RegExp → Ensemble String _
ℒ zeroᴿ    = λ _ → ⊥
ℒ oneᴿ     = λ xs → xs ≡ ε
ℒ (varᴿ a) = λ xs → xs ≡ a ∷ ε
ℒ (F +ᴿ G) = λ xs → xs ∈ ℒ F ⊎ xs ∈ ℒ G
ℒ (F *ᴿ G) = ℒ F ∙ ℒ G
ℒ (F ⋆ᴿ)   = (ℒ F) ⋆

data null : RegExp → Set 𝑎 where
  null-oneᴿ     : null oneᴿ
  null-+ᴿ-left  : ∀ {F G} → null F → null (F +ᴿ G)
  null-+ᴿ-right : ∀ {F G} → null G → null (F +ᴿ G)
  null-*ᴿ       : ∀ {F G} → null F → null G → null (F *ᴿ G)
  null-⋆ᴿ       : ∀ {F} → null (F ⋆ᴿ)

null-soundness : ∀ {F} → null F → ε ∈ ℒ F
null-soundness null-oneᴿ         = refl
null-soundness (null-+ᴿ-left p)  = inl (null-soundness p)
null-soundness (null-+ᴿ-right p) = inr (null-soundness p)
null-soundness (null-*ᴿ p q)     = [] , [] , (refl , null-soundness p) , null-soundness q
null-soundness null-⋆ᴿ           = 0 , refl

null-completeness : ∀ {F} → ε ∈ ℒ F → null F
null-completeness {oneᴿ}   _                       = null-oneᴿ
null-completeness {varᴿ a} ()
null-completeness {F +ᴿ G} (inl p)                 = null-+ᴿ-left (null-completeness p)
null-completeness {F +ᴿ G} (inr p)                 = null-+ᴿ-right (null-completeness p)
null-completeness {F *ᴿ G} (xs , ys , (p , q) , r)
  = null-*ᴿ (null-completeness (subst (_∈ ℒ F) (++-[]-cancel-left (sym p)) q))
            (null-completeness (subst (_∈ ℒ G) (++-[]-cancel-right (sym p)) r))
null-completeness {F ⋆ᴿ}   _                       = null-⋆ᴿ

null?-+ᴿ : ∀ {F G} → null (F +ᴿ G) → null F ⊎ null G
null?-+ᴿ = null-proj-helper
  where

  NullProj : RegExp → Set 𝑎
  NullProj zeroᴿ    = ⊤
  NullProj oneᴿ     = ⊤
  NullProj (varᴿ _) = ⊤
  NullProj (F +ᴿ G) = null F ⊎ null G
  NullProj (_ *ᴿ _) = ⊤
  NullProj (_ ⋆ᴿ)   = ⊤

  null-proj-helper : {F : RegExp} → null F → NullProj F
  null-proj-helper null-oneᴿ         = tt
  null-proj-helper (null-+ᴿ-left p)  = inl p
  null-proj-helper (null-+ᴿ-right p) = inr p
  null-proj-helper (null-*ᴿ p q)     = tt
  null-proj-helper null-⋆ᴿ           = tt

null?-*ᴿ : ∀ {F G} → null (F *ᴿ G) → null F × null G
null?-*ᴿ = null-proj-helper
  where

  NullProj : RegExp → Set 𝑎
  NullProj zeroᴿ    = ⊤
  NullProj oneᴿ     = ⊤
  NullProj (varᴿ _) = ⊤
  NullProj (_ +ᴿ _) = ⊤
  NullProj (F *ᴿ G) = null F × null G
  NullProj (_ ⋆ᴿ)   = ⊤

  null-proj-helper : {F : RegExp} → null F → NullProj F
  null-proj-helper null-oneᴿ         = tt
  null-proj-helper (null-+ᴿ-left p)  = tt
  null-proj-helper (null-+ᴿ-right p) = tt
  null-proj-helper (null-*ᴿ p q)     = p , q
  null-proj-helper null-⋆ᴿ           = tt

null? : ∀ F → Dec (null F)
null? zeroᴿ    = no (λ ())
null? oneᴿ     = yes null-oneᴿ
null? (varᴿ _) = no (λ ())
null? (F +ᴿ G) with null? F
... | yes p = yes (null-+ᴿ-left p)
... | no  p with null? G
...     | yes q = yes (null-+ᴿ-right q)
...     | no  q = no λ r → ⊎-elim p q (null?-+ᴿ r)
null? (F *ᴿ G) with null? F
...           | yes p with null? G
...               | yes q = yes (null-*ᴿ p q)
...               | no q = no λ r → q (snd (null?-*ᴿ r))
null? (F *ᴿ G) | no p = no λ r → p (fst (null?-*ᴿ r))
null? (F ⋆ᴿ)   = yes null-⋆ᴿ

_[_] : RegExp → A → RegExp
zeroᴿ    [ a ] = zeroᴿ
oneᴿ     [ a ] = zeroᴿ
varᴿ x   [ a ] with x ≟ a
... | yes p = oneᴿ
... | no  p = zeroᴿ
(F +ᴿ G) [ a ] = (F [ a ]) +ᴿ (G [ a ])
(F *ᴿ G) [ a ] with null? F
... | yes p = ((F [ a ]) *ᴿ G) +ᴿ (G [ a ])
... | no  p = (F [ a ]) *ᴿ G
(F ⋆ᴿ)   [ a ] = (F [ a ]) *ᴿ (F ⋆ᴿ)

derivative-soundness : ∀ {a xs F} → xs ∈ ℒ (F [ a ]) → (a ∷ xs) ∈ ℒ F
derivative-soundness {a} {F = varᴿ x} p with x ≟ a
... | yes q = trans (cong (_ ∷_) p) (cong (_∷ _) (sym q))
derivative-soundness {F = F +ᴿ G}     (inl p)
  = inl (derivative-soundness {F = F} p)
derivative-soundness {F = F +ᴿ G}     (inr p)
  = inr (derivative-soundness {F = G} p)
derivative-soundness {F = F *ᴿ G}     p with null? F
... | yes q = ⊎-elim (λ { (ys , zs , (r , s) , t) →
                            _ ∷ ys , zs , (cong _ r , derivative-soundness {F = F} s) , t})
                     (λ r → [] , _ , (refl , null-soundness q) , derivative-soundness {F = G} r)
                     p
derivative-soundness {F = F *ᴿ G}     (ys , zs , (p , q) , r)
    | no _ = _ ∷ ys , zs , (cong _ p , derivative-soundness {F = F} q) , r
derivative-soundness {F = F ⋆ᴿ}       (ys , zs , (p , q) , n , r)
  = suc n , _ ∷ ys , zs , (cong _ p , derivative-soundness {F = F} q) , r

derivative-completeness : ∀ {a xs F} → (a ∷ xs) ∈ ℒ F → xs ∈ ℒ (F [ a ])
derivative-completeness {a} {F = varᴿ x} p with x ≟ a
... | yes q = ∷-inj-right p
... | no  q = q (sym (∷-inj-left p))
derivative-completeness {F = F +ᴿ G} (inl p) = inl (derivative-completeness {F = F} p)
derivative-completeness {F = F +ᴿ G} (inr p) = inr (derivative-completeness {F = G} p)
derivative-completeness {F = F *ᴿ G} (ys , zs , (p , q) , r) with null? F
... | yes s with ys
...     | []     = inr (derivative-completeness {F = G} (subst (_∈ ℒ G) (sym p) r))
...     | y ∷ ys = inl (ys , zs , (∷-inj-right p , subst (λ x → ℒ (F [ x ]) ys)
                                                         (sym (∷-inj-left p))
                                                         (derivative-completeness {F = F} q)) , r)
derivative-completeness {F = F *ᴿ G} (ys , zs , (p , q) , r) | no  s with ys
... | []     = ⊥-elim (s (null-completeness q))
... | y ∷ ys = ys , zs , (∷-inj-right p , subst (λ x → ℒ (F [ x ]) ys)
                                                (sym (∷-inj-left p))
                                                (derivative-completeness {F = F} q)) , r
derivative-completeness {F = F ⋆ᴿ} (n , p) = h {F = F} {n = n} p
  where

  h : ∀ {a xs F n} → (a ∷ xs) ∈ (ℒ F ^ n) → xs ∈ ℒ ((F [ a ]) *ᴿ (F ⋆ᴿ))
  h {F = F} {n = suc n} (ys , zs , (p , q) , r) with ys
  ... | []     = h {F = F} {n} (subst (_∈ ℒ F ^ n) (sym p) r)
  ... | y ∷ ys = ys , zs , (∷-inj-right p , subst (λ x → ℒ (F [ x ]) ys)
                                                  (sym (∷-inj-left p))
                                                  (derivative-completeness {F = F} q)) , n , r

match : RegExp → String → Set _
match F xs = null (foldl _[_] F xs)

match-soundness : ∀ {xs F} → match F xs → xs ∈ ℒ F
match-soundness {[]}         p = null-soundness p
match-soundness {x ∷ xs} {F} p = derivative-soundness {F = F} (match-soundness {F = F [ x ]} p)

match-completeness : ∀ {xs F} → xs ∈ ℒ F → match F xs
match-completeness {[]}         p = null-completeness p
match-completeness {x ∷ xs} {F} p = match-completeness {xs = xs} (derivative-completeness {F = F} p)
