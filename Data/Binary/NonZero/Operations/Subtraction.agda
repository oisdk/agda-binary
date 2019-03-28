{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Subtraction where

open import Data.Binary.NonZero.Definitions
open import Data.Product as Product using (map₁; map₂; proj₁; proj₂; _,_; _×_)
open import Data.Bool
import Data.Maybe as Maybe
import Data.Binary.NonZero.Operations.Addition as +
open import Data.Binary.NonZero.Operations.Unary

-_ : 𝔹± → 𝔹±
-_ = Maybe.map (map₁ not)

-- mutual
--   sub₀ : 𝔹⁺ → 𝔹⁺ → 𝔹±
--   sub₀ xs 1⁺ = Maybe.map (O ,_) (dec⁺ xs)
--   sub₀ 1⁺ (y ⁺∷ ys) = Maybe.map (I ,_) (dec⁺ (y ⁺∷ ys))
--   sub₀ (0⁺∷ xs) (0⁺∷ ys) = Maybe.map (map₂ (O ⁺∷_)) (sub₀ xs ys)
--   sub₀ (0⁺∷ xs) (1⁺∷ ys) = Maybe.map (map₂ (I ⁺∷_)) (sub₁ xs ys)
--   sub₀ (1⁺∷ xs) (0⁺∷ ys) = Maybe.map (map₂ (I ⁺∷_)) (sub₀ xs ys)
--   sub₀ (1⁺∷ xs) (1⁺∷ ys) = Maybe.map (map₂ (O ⁺∷_)) (sub₀ xs ys)

--   sub₁ : 𝔹⁺ → 𝔹⁺ → 𝔹±
--   sub₁ 1⁺ ys = 0< (I , ys)
--   sub₁ (x ⁺∷ xs) 1⁺ = {!!}
--   sub₁ (x ⁺∷ xs) (y ⁺∷ ys) = {!!}

-- _+_ : 𝔹± → 𝔹± → 𝔹±
-- 0ᵇ + ys = ys
-- (0< xs) + 0ᵇ = 0< xs
-- (0< (O , xs)) + (0< (O , ys)) = 0< (O , +.add₀ xs ys)
-- (0< (O , xs)) + (0< (I , ys)) = sub₀ xs ys
-- (0< (I , xs)) + (0< (O , ys)) = sub₀ ys xs
-- (0< (I , xs)) + (0< (I , ys)) = 0< (I , +.add₀ xs ys)
