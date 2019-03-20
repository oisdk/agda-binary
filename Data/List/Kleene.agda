{-# OPTIONS --without-K --safe #-}

module Data.List.Kleene where

infixr 5 _&_
mutual
  record _⁺  {a} (A : Set a) : Set a where
    inductive
    constructor _&_
    field
      head : A
      tail : A ⋆

  data _⋆ {a} (A : Set a) : Set a where
    [] : A ⋆
    [_] : A ⁺ → A ⋆

open _⁺ public
