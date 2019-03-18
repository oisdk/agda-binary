{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Properties where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Segmented
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary
open import Function

dec-inc : ∀ x → dec⁺ (inc⁺ x) ≡ x
dec-inc 0₂                         = refl
dec-inc (0< B₁ _ 1& 0₂           ) = refl
dec-inc (0< B₁ _ 1& 0< zero  0& _) = refl
dec-inc (0< B₁ _ 1& 0< suc _ 0& _) = refl
dec-inc (0< B₀ zero  0& _        ) = refl
dec-inc (0< B₀ suc _ 0& _        ) = refl

inc-dec : ∀ x → inc⁺ (dec⁺ x) ≡ x
inc-dec (     B₁ zero  1& 0₂  ) = refl
inc-dec (     B₁ zero  1& 0< _) = refl
inc-dec (     B₁ suc _ 1& _   ) = refl
inc-dec (B₀ _ 0& zero  1& 0₂  ) = refl
inc-dec (B₀ _ 0& zero  1& 0< _) = refl
inc-dec (B₀ _ 0& suc _ 1& _   ) = refl

mutual
  infix 4 _≟₀_ _≟₁_ _≟≤_
  _≟₀_ : Decidable (_≡_ {A = Bits₀})
  x 0& xs ≟₀ y 0& ys with x ℕ.≟ y
  x 0& xs ≟₀ y 0& ys | no ¬p = no λ { refl → ¬p refl }
  x 0& xs ≟₀ y 0& ys | yes p with xs ≟₁ ys
  x 0& xs ≟₀ y 0& ys | yes p | no ¬p = no λ { refl → ¬p refl }
  x 0& xs ≟₀ .x 0& .xs | yes refl | yes refl = yes refl

  _≟₁_ : Decidable (_≡_ {A = Bits₁})
  x 1& xs ≟₁ y 1& ys with x ℕ.≟ y
  x 1& xs ≟₁ y 1& ys | no ¬p = no λ { refl → ¬p refl }
  x 1& xs ≟₁ y 1& ys | yes p with xs ≟≤ ys
  x 1& xs ≟₁ y 1& ys | yes p | no ¬p = no λ { refl → ¬p refl }
  x 1& xs ≟₁ y 1& ys | yes refl | yes refl = yes refl

  _≟≤_ : Decidable (_≡_ {A = 0≤ Bits₀})
  0₂ ≟≤ 0₂ = yes refl
  0₂ ≟≤ 0< _ = no (λ ())
  0< _ ≟≤ 0₂ = no (λ ())
  0< xs ≟≤ 0< ys with xs ≟₀ ys
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }

infix 4 _≟_
_≟_ : Decidable (_≡_ {A = Bits})
0₂ ≟ 0₂ = yes refl
0₂ ≟ (0< x) = no (λ ())
(0< x) ≟ 0₂ = no (λ ())
(0< B₀ xs) ≟ (0< B₀ ys) with xs ≟₀ ys
(0< B₀ xs ≟ 0< B₀ .xs) | yes refl = yes refl
(0< B₀ xs ≟ 0< B₀ ys) | no ¬p = no λ { refl → ¬p refl }
(0< B₀ xs) ≟ (0< B₁ ys) = no (λ ())
(0< B₁ x) ≟ (0< B₀ x₁) = no (λ ())
(0< B₁ xs) ≟ (0< B₁ ys) with xs ≟₁ ys
(0< B₁ x ≟ 0< B₁ x₁) | yes refl = yes refl
(0< B₁ x ≟ 0< B₁ x₁) | no ¬p = no λ { refl → ¬p refl }

open ≡-Reasoning
import Data.Nat.Properties as ℕ-Prop
open import Data.Empty

lemma₁ : ∀ x {y} → x ≢ 0 → x ℕ.+ y ≢ 0
lemma₁ zero = λ z _ → z refl
lemma₁ (suc x) = λ _ ()

lemma₂ : ∀ {x} → x ≢ 0 → ℕ.pred (2 ℕ.* x) ≡ suc (2 ℕ.* ℕ.pred x)
lemma₂ {zero} p = ⊥-elim (p refl)
lemma₂ {suc x} _ = ℕ-Prop.+-suc _ _

lemma₄ : ∀ x → 2 ℕ.^ x ≢ 0
lemma₄ zero = λ ()
lemma₄ (suc x) = lemma₁ _ (lemma₄ x)

lemma₅ : ∀ x y → x ≢ 0 → y ≢ 0 → x ℕ.* y ≢ 0
lemma₅ zero y x≢0 y≢0 = λ _ → x≢0 refl
lemma₅ (suc x) zero x≢0 y≢0 = λ _ → y≢0 refl
lemma₅ (suc x) (suc y) x≢0 y≢0 = λ ()

lemma₃ : ∀ x → ⟦ x ⇓⟧₁⁺¹ ≢ 0
lemma₃ (x 1& xs) = lemma₅ (2 ℕ.^ suc x) (suc ⟦ xs ⇓⟧≤) (lemma₄ (suc x)) λ ()

inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-homo 0₂ = refl
inc-homo (0< B₀ zero  0& y 1& xs) =
  begin
    ℕ.pred ⟦ suc y 1& xs ⇓⟧₁⁺¹
  ≡⟨⟩
    ℕ.pred (2 ℕ.^ suc (suc y) ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨⟩
    ℕ.pred (2 ℕ.* 2 ℕ.^ suc y ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨ cong ℕ.pred (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc y) _) ⟩
    ℕ.pred (2 ℕ.* (2 ℕ.^ suc y ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    ℕ.pred (2 ℕ.* ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨ lemma₂ (lemma₃ (y 1& xs)) ⟩
    suc (2 ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc (2 ℕ.^ 1 ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc ⟦ 0 0& y 1& xs ⇓⟧₀
  ∎
inc-homo (0< B₀ suc x 0& y 1& xs) =
  begin
    (2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤) ℕ.+
      suc ((2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤) ℕ.+ zero)
  ≡⟨ ℕ-Prop.+-suc _ _ ⟩
    suc (2 ℕ.* ((2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤)))
  ≡⟨ cong suc (sym (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc x) _)) ⟩
    suc ((2 ℕ.^ suc (suc x)) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    suc ⟦ suc x 0& y 1& xs ⇓⟧₀
  ∎
inc-homo (0< B₁ x 1& 0₂) =
  begin
    ⟦ x 0& 0 1& 0₂ ⇓⟧₀
  ≡⟨⟩
    ⟦ x 1& 0₂ ⇓⟧₁⁺¹
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (lemma₃ (x 1& 0₂))) ⟩
    suc (ℕ.pred ⟦ x 1& 0₂ ⇓⟧₁⁺¹)
  ∎
inc-homo (0< B₁ x 1& 0< zero  0& z 1& xs) =
  begin
    ⟦ x 0& suc z 1& xs ⇓⟧₀
  ≡⟨⟩
    (2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.* 2 ℕ.^ suc z) ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (cong ℕ.pred (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc z) _)) ⟩
    (2 ℕ.^ suc x) ℕ.* ℕ.pred (2 ℕ.* (2 ℕ.^ suc z ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    (2 ℕ.^ suc x) ℕ.* ℕ.pred (2 ℕ.* ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (lemma₂ (lemma₃ (z 1& xs))) ⟩
    (2 ℕ.^ suc x) ℕ.* suc (2 ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    ⟦ x 1& 0< zero 0& z 1& xs ⇓⟧₁⁺¹
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (lemma₃ (x 1& 0< 0 0& z 1& xs))) ⟩
    suc (ℕ.pred ⟦ x 1& 0< zero 0& z 1& xs ⇓⟧₁⁺¹)
  ∎
inc-homo (0< B₁ x 1& 0< suc y 0& z 1& xs) =
  begin
    ⟦ x 0& 0 1& 0< y 0& z 1& xs ⇓⟧₀
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* ℕ.pred ⟦ 0 1& 0< y 0& z 1& xs ⇓⟧₁⁺¹
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* ℕ.pred (2 ℕ.* suc ⟦ y 0& z 1& xs ⇓⟧₀)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (lemma₂ {x = suc ⟦ y 0& z 1& xs ⇓⟧₀} λ ()) ⟩
    2 ℕ.^ suc x ℕ.* suc (2 ℕ.* ⟦ y 0& z 1& xs ⇓⟧₀)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (cong suc (sym (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc y) _))) ⟩
    2 ℕ.^ suc x ℕ.* suc (2 ℕ.* 2 ℕ.^ suc y ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* suc (2 ℕ.^ suc (suc y) ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* suc ⟦ suc y 0& z 1& xs ⇓⟧₀
  ≡⟨⟩
    ⟦ x 1& 0< suc y 0& z 1& xs ⇓⟧₁⁺¹
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (lemma₃ (x 1& 0< suc y 0& z 1& xs))) ⟩
    suc (ℕ.pred ⟦ x 1& 0< suc y 0& z 1& xs ⇓⟧₁⁺¹)
  ∎

homo : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
homo zero = refl
homo (suc n) = inc-homo ⟦ n ⇑⟧ ⟨ trans ⟩ cong suc (homo n)

data Suc-View : Bits → Set where
  zeroᵇ : Suc-View 0₂
  sucᵇ : ∀ x → Suc-View (inc x)

suc-view : ∀ x → Suc-View x
suc-view 0₂ = zeroᵇ
suc-view (0< xs) = subst Suc-View (cong 0<_ (inc-dec xs)) (sucᵇ (dec⁺ xs))

⟦x⇓⟧⁺≢0 : ∀ x → ⟦ x ⇓⟧⁺ ≢ 0
⟦x⇓⟧⁺≢0 x p with suc-view (0< x)
⟦x⇓⟧⁺≢0 .(inc⁺ x) p | sucᵇ x with sym (inc-homo x) ⟨ trans ⟩ p
⟦x⇓⟧⁺≢0 .(inc⁺ x) p | sucᵇ x | ()

data Suc-Rec : Bits → Set where
  zeroʳ : Suc-Rec 0₂
  sucʳ : ∀ x → Suc-Rec x → Suc-Rec (inc x)

suc-rec : ∀ x → Suc-Rec x
suc-rec x = go _ x (inspect ⟦_⇓⟧ x)
  where
  go : ∀ n x → Reveal ⟦_⇓⟧ · x is n → Suc-Rec x
  go n 0₂ p = zeroʳ
  go zero (0< x) [ p ] = ⊥-elim (⟦x⇓⟧⁺≢0 x p)
  go (suc n) (0< xs) [ p ] = subst Suc-Rec (cong 0<_ (inc-dec xs)) (sucʳ (dec⁺ xs) (go n (dec⁺ xs) [ ℕ-Prop.suc-injective (sym (inc-homo (dec⁺ xs)) ⟨ trans ⟩ cong ⟦_⇓⟧⁺ (inc-dec xs)  ⟨ trans ⟩ p) ]))

inj : ∀ x y → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
inj x y = go (suc-rec x) (suc-rec y)
  where
  go : ∀ {x y} → Suc-Rec x → Suc-Rec y → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
  go {x} {y} x′ y′ ⟦x⇓⟧≡⟦y⇓⟧ with ⟦ x ⇓⟧ | ⟦ y ⇓⟧ | inspect ⟦_⇓⟧ x | inspect ⟦_⇓⟧ y
  go zeroʳ zeroʳ ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] = refl
  go (sucʳ x′ xs′) zeroʳ ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo x′) ⟨ trans ⟩ x≡ ⟨ trans ⟩ ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym y≡
  go {.(0< inc⁺ x′)} {.0₂} (sucʳ x′ xs′) zeroʳ ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | ()
  go zeroʳ (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo y′) ⟨ trans ⟩ y≡ ⟨ trans ⟩ sym ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym x≡
  go {.0₂} {.(0< inc⁺ y′)} zeroʳ (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | ()
  go (sucʳ x′ xs′) (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo x′) ⟨ trans ⟩ x≡ ⟨ trans ⟩ ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym (sym (inc-homo y′) ⟨ trans ⟩ y≡)
  go (sucʳ x′ xs′) (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | x′≡y′ = cong inc (go xs′ ys′ (ℕ-Prop.suc-injective x′≡y′))

open import Function.Bijection

𝔹↔ℕ : Bits ⤖ ℕ
𝔹↔ℕ = bijection ⟦_⇓⟧ ⟦_⇑⟧ (λ {x} {y} → inj x y) homo
