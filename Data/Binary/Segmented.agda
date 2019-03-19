{-# OPTIONS --without-K #-}

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

inc₁ : 𝔹₁ → 𝔹₀
inc₁ (x 1& 0₂                 ) = x 0& 0     1& 0₂
inc₁ (x 1& 0< zero  0& z 1& xs) = x 0& suc z 1& xs
inc₁ (x 1& 0< suc y 0& z 1& xs) = x 0& 0     1& 0< y 0& z 1& xs

inc₀ : 𝔹₀ → 𝔹₁
inc₀ (zero  0& y 1& xs) = suc y 1& xs
inc₀ (suc x 0& y 1& xs) = 0     1& 0< x 0& y 1& xs

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0₂         = B₁ 0 1& 0₂
inc⁺ (0< B₀ xs) = B₁ (inc₀ xs)
inc⁺ (0< B₁ xs) = B₀ (inc₁ xs)

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
  add₀? (0< x₀ 0& xs) y₀ ys = add₀ x₀ xs y₀ ys

  add₀ : ℕ → 𝔹₁
       → ℕ → 𝔹₁
       → 𝔹₀
  add₀ x₀ xs y₀ ys with ℕ.compare x₀ y₀
  add₀ x₀ (x₁ 1& xs) _  ys         | ℕ.less _ k    = x₀ 0& add₁ x₁ xs k ys
  add₀ x₀ (x₁ 1& xs) _  ys         | ℕ.equal _     = cncZero x₀ (add₂ x₁ xs ys)
  add₀ _  xs         y₀ (y₁ 1& ys) | ℕ.greater _ k = y₀ 0& add₁ y₁ ys k xs

  add₁? : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  add₁? x₁ xs 0₂ = x₁ 1& xs
  add₁? x₁ xs (0< y₀ 0& ys) = add₁ x₁ xs y₀ ys

  add₁ : ℕ → 0≤ 𝔹₀
       → ℕ → 𝔹₁
       → 𝔹₁
  add₁ x₁ xs y₀ ys with ℕ.compare x₁ y₀
  add₁ x₁ xs _  ys         | ℕ.less .x₁ k    = x₁ 1& 0< add₀? xs k ys
  add₁ x₁ xs _  (y₁ 1& ys) | ℕ.equal .x₁     = cncOne x₁ (add₁? y₁ ys xs)
  add₁ _  xs y₀ ys         | ℕ.greater .y₀ k = y₀ 1& 0< add₂ k xs ys

  add₂ : ℕ → 0≤ 𝔹₀
       → 𝔹₁
       → 𝔹₀
  add₂ x₁ xs (y₁ 1& ys) with ℕ.compare x₁ y₁
  add₂ 0      xs (_  1& ys)   | ℕ.less _ k    = cncZero 0 (add₁′? k ys xs)
  add₂ (suc x₁) xs (_  1& ys) | ℕ.less _ k    = 0 0& x₁ 1& 0< add₁′? k ys xs
  add₂ x₁ xs (_  1& ys)       | ℕ.equal .x₁   = 0 0& cncOne′ x₁ (add₀′?? xs ys)
  add₂ _  xs (0      1& ys)   | ℕ.greater _ k = cncZero 0 (add₁′? k xs ys)
  add₂ _  xs (suc y₁ 1& ys)   | ℕ.greater _ k = 0 0& y₁ 1& 0< add₁′? k xs ys

  add₀′? : 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  add₀′? 0₂ y₀ ys = inc₀ (y₀ 0& ys)
  add₀′? (0< xs) y₀ ys = add₀′ xs y₀ ys

  add₀′?? : 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  add₀′?? 0₂ 0₂ = 0 1& 0₂
  add₀′?? 0₂ (0< xs) = inc₀ xs
  add₀′?? (0< xs) 0₂ = inc₀ xs
  add₀′?? (0< xs) (0< y₀ 0& ys) = add₀′ xs y₀ ys

  add₀′ : 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  add₀′ (x₀ 0& xs) y₀  ys with ℕ.compare x₀ y₀
  add₀′ (0      0& x₁ 1& xs) _       ys         | ℕ.less _ k    = cncOne 0 (add₁ x₁ xs k ys)
  add₀′ (suc x₀ 0& x₁ 1& xs) _       ys         | ℕ.less _ k    = 0 1& 0< x₀ 0& add₁ x₁ xs k ys
  add₀′ (x₀     0& x₁ 1& xs) _       ys         | ℕ.equal _     = 0 1& 0< cncZero′ x₀ (add₂ x₁ xs ys)
  add₀′ (_      0& xs)      0        (y₁ 1& ys) | ℕ.greater _ k = cncOne 0 (add₁ y₁ ys k xs)
  add₀′ (_      0& xs)      (suc y₀) (y₁ 1& ys) | ℕ.greater _ k = 0 1& 0< y₀ 0& add₁ y₁ ys k xs

  add₁′? : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₀
  add₁′? x xs 0₂ = inc₁ (x 1& xs)
  add₁′? x xs (0< ys) = add₁′ x xs ys

  add₁′ : ℕ → 0≤ 𝔹₀ → 𝔹₀ → 𝔹₀
  add₁′ x₁ xs (y₀ 0& ys) with ℕ.compare x₁ y₀
  add₁′ x₁ xs (_  0& ys)       | ℕ.less .x₁ k    = x₁ 0& (add₀′? xs k ys)
  add₁′ x₁ xs (_  0& y₁ 1& ys) | ℕ.equal .x₁     = cncZero x₁ (add₁′? y₁ ys xs)
  add₁′ _  xs (y₀ 0& ys)       | ℕ.greater .y₀ k = y₀ 0& add₂′ k xs ys

  add₂′ : ℕ → 0≤ 𝔹₀ → 𝔹₁ → 𝔹₁
  add₂′ x₁ xs (y₁ 1& ys) with ℕ.compare x₁ y₁
  add₂′ x₁ xs (_  1& ys) | ℕ.less _ k    = x₁ 1& 0< add₁′? k ys xs
  add₂′ x₁ xs (_  1& ys) | ℕ.equal .x₁   = cncOne x₁ (add₀′?? xs ys)
  add₂′ _  xs (y₁ 1& ys) | ℕ.greater _ k = y₁ 1& 0< add₁′? k xs ys

  cncZero : ℕ → 𝔹₀ → 𝔹₀
  cncZero n (x 0& xs) = suc (n ℕ.+ x) 0& xs

  cncOne : ℕ → 𝔹₁ → 𝔹₁
  cncOne n (x 1& xs) = suc (n ℕ.+ x) 1& xs

  cncOne′ : ℕ → 𝔹₁ → 𝔹₁
  cncOne′ 0 xs = xs
  cncOne′ (suc n) = cncOne n

  cncZero′ : ℕ → 𝔹₀ → 𝔹₀
  cncZero′ 0 xs = xs
  cncZero′ (suc n) = cncZero n

_+_ : 𝔹 → 𝔹 → 𝔹
0₂ + ys = ys
(0< xs) + 0₂ = 0< xs
(0< B₀ x 0& xs) + (0< B₀ y 0& ys) = 0< B₀ add₀ x xs y ys
(0< B₀ x 0& xs) + (0< B₁ y₁ 1& ys) = 0< B₁ add₁ y₁ ys x xs
(0< B₁ x₁ 1& xs) + (0< B₀ y 0& ys) = 0< B₁ add₁ x₁ xs y ys
(0< B₁ x₁ 1& xs) + (0< B₁ ys) = 0< B₀ add₂ x₁ xs ys

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
