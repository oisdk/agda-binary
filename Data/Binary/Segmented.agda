{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product as Product using (_×_; _,_)
open import Function

data 0≤_ (A : Set) : Set where
  0₂ : 0≤ A
  0<_ : A → 0≤ A

infixr 5 _0&_ _1&_ B₀_ B₁_ 0<_
mutual
  record 𝔹₀ : Set where
    constructor _0&_
    inductive
    field
      zeroes : ℕ
      tail₁ : 𝔹₁

  record 𝔹₁ : Set where
    constructor _1&_
    inductive
    field
      ones : ℕ
      tail₀ : 0≤  𝔹₀

  data 𝔹⁺ : Set where
    B₀_ : 𝔹₀ → 𝔹⁺
    B₁_ : 𝔹₁ → 𝔹⁺

  𝔹 : Set
  𝔹 = 0≤ 𝔹⁺
open 𝔹₀
open 𝔹₁

inc₁ : 0≤ 𝔹₀ → 𝔹₁
inc₁ (0₂                 ) = 0     1& 0₂
inc₁ (0< zero  0& z 1& xs) = suc z 1& xs
inc₁ (0< suc y 0& z 1& xs) = 0     1& 0< y 0& z 1& xs

inc₀ : 𝔹₀ → 𝔹₁
inc₀ (zero  0& y 1& xs) = suc y 1& xs
inc₀ (suc x 0& y 1& xs) = 0     1& 0< x 0& y 1& xs

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0₂         = B₁ 0 1& 0₂
inc⁺ (0< B₀ xs) = B₁ (inc₀ xs)
inc⁺ (0< B₁ x 1& xs) = B₀ (x 0& inc₁ xs)

inc : 𝔹 → 𝔹
inc x = 0< inc⁺ x

dec⁺ : 𝔹⁺ → 𝔹
dec⁺ (     B₁ zero  1& 0₂)         = 0₂
dec⁺ (     B₁ zero  1& 0< x 0& xs) = 0< B₀ suc x 0& xs
dec⁺ (     B₁ suc y 1& xs)         = 0< B₀ 0     0& y 1& xs
dec⁺ (B₀ x 0& zero  1& 0₂)         = 0<          B₁ x 1& 0₂
dec⁺ (B₀ x 0& zero  1& 0< y 0& xs) = 0<          B₁ x 1& 0< suc y  0& xs
dec⁺ (B₀ x 0& suc y 1& xs)         = 0<          B₁ x 1& 0< 0 0& y 1& xs

dec : 𝔹 → 𝔹
dec 0₂ = 0₂
dec (0< x) = dec⁺ x

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0₂
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

mutual
  ⟦_⇓⟧≤ : 0≤ 𝔹₀ → ℕ
  ⟦ 0₂ ⇓⟧≤ = 0
  ⟦ 0< xs ⇓⟧≤ = ⟦ xs ⇓⟧₀

  ⟦_⇓⟧₁⁺¹ : 𝔹₁ → ℕ
  ⟦ x 1& xs ⇓⟧₁⁺¹ = 2 ℕ.^ suc x ℕ.* suc ⟦ xs ⇓⟧≤

  ⟦_⇓⟧₀ : 𝔹₀ → ℕ
  ⟦ x 0& xs ⇓⟧₀ = 2 ℕ.^ suc x ℕ.* ℕ.pred ⟦ xs ⇓⟧₁⁺¹

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦ B₀ xs ⇓⟧⁺ = ⟦ xs ⇓⟧₀
⟦ B₁ xs ⇓⟧⁺ = ℕ.pred ⟦ xs ⇓⟧₁⁺¹

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0₂ ⇓⟧ = 0
⟦ 0< xs ⇓⟧ = ⟦ xs ⇓⟧⁺

mutual
  add₀? : 0≤ 𝔹₀
        → ℕ → 𝔹₁
        → 𝔹₀
  add₀? 0₂ y₀ ys = y₀ 0& ys
  add₀? (0< x₀ 0& xs) y₀ ys = add₀ 0 x₀ xs y₀ ys

  add₀ : ℕ → ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₀
  add₀ c zero     (x₁ 1& xs) zero     (y₁ 1& ys) = add₂ (suc c) x₁ xs y₁ ys
  add₀ c zero     (x₁ 1& xs) (suc y₀) ys         = c 0& add₁ 0 x₁ xs y₀ ys
  add₀ c (suc x₀) xs         zero     (y₁ 1& ys) = c 0& add₁ 0 y₁ ys x₀ xs
  add₀ c (suc x₀) xs         (suc y₀) ys         = add₀ (suc c) x₀ xs y₀ ys

  add₁? : ℕ → ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  add₁? c x₁ xs 0₂ = c ℕ.+ x₁ 1& xs
  add₁? c x₁ xs (0< y₀ 0& ys) = add₁ c x₁ xs y₀ ys

  add₁ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  add₁ c zero     xs zero     (y₁ 1& ys) = add₁? (suc c) y₁ ys xs
  add₁ c zero     xs (suc y₀) ys         = c 1& 0< add₀? xs y₀ ys
  add₁ c (suc x₁) xs zero     (y₁ 1& ys) = c 1& 0< add₂ 0 x₁ xs y₁ ys
  add₁ c (suc x₁) xs (suc y₀) ys         = add₁ (suc c) x₁ xs y₀ ys

  add₂ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₀
  add₂ c zero     xs zero     ys = c 0& add₀′?? 0 xs ys
  add₂ c zero     xs (suc y₁) ys = add₁′? (suc c) y₁ ys xs
  add₂ c (suc x₁) xs zero     ys = add₁′? (suc c) x₁ xs ys
  add₂ c (suc x₁) xs (suc y₁) ys = add₂″ 0 c x₁ xs y₁ ys

  add₂″ : ℕ → ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₀
  add₂″ d c zero     xs zero     ys = c 0& add₀′?? (suc d) xs ys
  add₂″ d c zero     xs (suc y₁) ys = c 0& d 1& 0< add₁′? 0 y₁ ys xs
  add₂″ d c (suc x₁) xs zero     ys = c 0& d 1& 0< add₁′? 0 x₁ xs ys
  add₂″ d c (suc x₁) xs (suc y₁) ys = add₂″ (suc d) c x₁ xs y₁ ys

  add₀′? : ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  add₀′? c 0₂ y₀ ys = cncOne′ c ( (y₀ 0& ys))
  add₀′? c (0< x₀ 0& xs) y₀ ys = add₀′ c x₀ xs y₀ ys

  add₀′?? : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  add₀′?? c 0₂ 0₂ = c 1& 0₂
  add₀′?? c 0₂ (0< xs) = cncOne′ c ( xs)
  add₀′?? c (0< xs) 0₂ = cncOne′ c ( xs)
  add₀′?? c (0< x₀ 0& xs) (0< y₀ 0& ys) = add₀′ c x₀ xs y₀ ys

  add₀′ : ℕ → ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₁
  add₀′ c zero     (x₁ 1& xs) zero     (y₁ 1& ys) = c 1& 0< add₂ 0 x₁ xs y₁ ys
  add₀′ c zero     (x₁ 1& xs) (suc y₀) ys         = add₁ (suc c) x₁ xs y₀ ys
  add₀′ c (suc x₀) xs         zero     (y₁ 1& ys) = add₁ (suc c) y₁ ys x₀ xs
  add₀′ c (suc x₀) xs         (suc y₀) ys         = add₀″ 0 c x₀ xs y₀ ys

  add₀″ : ℕ → ℕ → ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₁
  add₀″ d c zero     (x₁ 1& xs) zero     (y₁ 1& ys) = c 1& 0< add₂ (suc d) x₁ xs y₁ ys
  add₀″ d c zero     (x₁ 1& xs) (suc y₀) ys         = c 1& 0< d 0& add₁ 0 x₁ xs y₀ ys
  add₀″ d c (suc x₀) xs         zero     (y₁ 1& ys) = c 1& 0< d 0& add₁ 0 y₁ ys x₀ xs
  add₀″ d c (suc x₀) xs         (suc y₀) ys         = add₀″ (suc d) c x₀ xs y₀ ys

  add₁′? : ℕ → ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₀
  add₁′? c x xs 0₂ = (c ℕ.+ x) 0& inc₁ xs
  add₁′? c x xs (0< y₀ 0& ys) = add₁′ c x xs y₀ ys

  add₁′ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₀
  add₁′ c zero     xs zero     (y₁ 1& ys) = add₁′? (suc c) y₁ ys xs
  add₁′ c zero     xs (suc y₀) ys         = c 0& add₀′? 0 xs y₀ ys
  add₁′ c (suc x₁) xs zero     (y₁ 1& ys) = c 0& add₂′ 0 x₁ xs y₁ ys
  add₁′ c (suc x₁) xs (suc y₀) ys         = add₁′ (suc c) x₁ xs y₀ ys

  add₂′ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₁
  add₂′ c zero     xs zero     ys = add₀′?? (suc c) xs ys
  add₂′ c zero     xs (suc y₁) ys = c 1& 0< add₁′? 0 y₁ ys xs
  add₂′ c (suc x₁) xs zero     ys = c 1& 0< add₁′? 0 x₁ xs ys
  add₂′ c (suc x₁) xs (suc y₁) ys = add₂′ (suc c) x₁ xs y₁ ys

  cncOne′ : ℕ → 𝔹₀ → 𝔹₁
  cncOne′ 0 (zero 0& y 1& xs) = suc y 1& xs
  cncOne′ 0 (suc x 0& y 1& xs) = 0 1& 0< x 0& y 1& xs
  cncOne′ (suc n) (zero  0& y 1& xs) = suc (suc (n ℕ.+ y)) 1& xs
  cncOne′ (suc n) (suc x 0& y 1& xs) = suc n 1& 0< x 0& y 1& xs

_+_ : 𝔹 → 𝔹 → 𝔹
0₂ + ys = ys
(0< xs) + 0₂ = 0< xs
(0< B₀ x 0& xs) + (0< B₀ y 0& ys) = 0< B₀ add₀ 0 x xs y ys
(0< B₀ x 0& xs) + (0< B₁ y₁ 1& ys) = 0< B₁ add₁ 0 y₁ ys x xs
(0< B₁ x₁ 1& xs) + (0< B₀ y 0& ys) = 0< B₁ add₁ 0 x₁ xs y ys
(0< B₁ x₁ 1& xs) + (0< B₁ y₁ 1& ys) = 0< B₀ add₂ 0 x₁ xs y₁ ys

open import Relation.Binary.PropositionalEquality
open import Data.List as List using (List; _∷_; [])

addProp : List (ℕ × ℕ) → Set
addProp xs = List.map (λ { (x , y) → ⟦ ⟦ x ⇑⟧ + ⟦ y ⇑⟧ ⇓⟧ }) xs ≡ List.map (λ { (x , y) →  x ℕ.+ y } ) xs

select : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
select [] ys = []
select (x ∷ xs) ys = List.foldr (λ y zs → (x , y) ∷ zs) (select xs ys) ys

nums : ℕ → List (ℕ × ℕ)
nums n = select (List.upTo n) (List.upTo n)

_ : addProp (nums 60)
_ = refl
