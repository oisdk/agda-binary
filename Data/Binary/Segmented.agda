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

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Bool as Bool using (Bool; true; false; _xor_; _∧_; not; _∨_)

uncons : 𝔹 → Maybe (Bool × 𝔹)
uncons 0₂ = nothing
uncons (0< B₀ zero 0& xs) = just (false , 0< B₁ xs)
uncons (0< B₀ suc x 0& xs) = just (false , 0< B₀ x 0& xs)
uncons (0< B₁ zero 1& 0₂) = just (true , 0₂)
uncons (0< B₁ zero 1& 0< xs) = just (true , 0< B₀ xs)
uncons (0< B₁ suc x 1& xs) = just (true , 0< B₁ x 1& xs)

infixr 5 0∷_ 1∷_ _∷𝔹_
0∷_ : 𝔹 → 𝔹
0∷ 0₂ = 0₂
0∷ (0< B₀ x 0& xs) = 0< B₀ suc x 0& xs
0∷ (0< B₁ xs) = 0< B₀ 0 0& xs

1∷_ : 𝔹 → 𝔹
1∷ 0₂ = 0< B₁ 0 1& 0₂
1∷ 0< B₀ xs = 0< B₁ 0 1& 0< xs
1∷ 0< B₁ x 1& xs = 0< B₁ suc x 1& xs

_∷𝔹_ : Bool → 𝔹 → 𝔹
false ∷𝔹 xs = 0∷ xs
true  ∷𝔹 xs = 1∷ xs

{-# TERMINATING #-}
add : Bool → Maybe (Bool × 𝔹) → Maybe (Bool × 𝔹) → 𝔹
add false (just (x , xs)) (just (y , ys)) = (x xor y) ∷𝔹 add (x ∧ y) (uncons xs) (uncons ys)
add false (just (x , xs)) nothing         = x ∷𝔹 xs
add false nothing         (just (y , ys)) = y ∷𝔹 ys
add false nothing         nothing         = 0₂
add true  (just (x , xs)) (just (y , ys)) = not (x xor y) ∷𝔹 add (x ∨ y) (uncons xs) (uncons ys)
add true  (just (x , xs)) nothing         = inc (x ∷𝔹 xs)
add true  nothing         (just (y , ys)) = inc (y ∷𝔹 ys)
add true  nothing         nothing         = inc 0₂

_+_ : 𝔹 → 𝔹 → 𝔹
xs + ys = add false (uncons xs) (uncons ys)

open import Data.List as List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality

addProp : List (ℕ × ℕ) → Set
addProp xs = List.map (λ { (x , y) → ⟦ x ⇑⟧ + ⟦ y ⇑⟧ }) xs ≡ List.map (λ { (x , y) →  ⟦ x ℕ.+ y ⇑⟧ } ) xs

select : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
select [] ys = []
select (x ∷ xs) ys = List.foldr (λ y ys → (x , y) ∷ ys) (select xs ys) ys

nums : ℕ → List (ℕ × ℕ)
nums n = select (List.upTo n) (List.upTo n)

_ : addProp (nums 20)
_ = refl
