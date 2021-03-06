module Ring where

open import Data.Bool
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function
open ≡-Reasoning


record Ring (A : Set) : Set where 
  infixl 4 _+_
  infixl 5 _*_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    zero : A
    one : A
    inv : A → A

    +-assoc : (a b c : A) → a + (b + c) ≡ (a + b) + c
    zero-+-id-left : (a : A) → zero + a ≡ a
    zero-+-id-right : (a : A) → a + zero ≡ a
    inv-+-left : (a : A) → (inv a) + a ≡ zero
    inv-+-right : (a : A) → a + (inv a) ≡ zero
    +-comm : (a b : A) → a + b ≡ b + a
  
    *-assoc : (a b c : A) → a * (b * c) ≡ (a * b) * c
    one-*-id-left : (a : A) → one * a ≡ a
    one-*-id-right : (a : A) → a * one ≡ a
  
    *-dist-+-left : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    *-dist-+-right : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)


module RingProperties (A : Set) (r : Ring A) where
  open Ring r

  +-unique-inv : (a ia : A) → (ia + a ≡ zero) → (ia ≡ inv a)
  +-unique-inv a ia eq = begin
    ia                       ≡⟨ (sym (zero-+-id-right ia)) ⟩
    ia + zero                ≡⟨ cong (λ x → ia + x) (sym (inv-+-right a)) ⟩
    ia + (a + inv a)         ≡⟨ +-assoc ia a (inv a) ⟩
    ia + a + inv a           ≡⟨ cong (λ x → x + inv a) eq ⟩
    zero + inv a             ≡⟨ zero-+-id-left (inv a) ⟩
    inv a
    ∎

  zero*a-zero : (a : A) → zero * a ≡ zero
  zero*a-zero a = begin
    zero * a                               ≡⟨ sym (zero-+-id-right (zero * a)) ⟩
    zero * a + zero                        ≡⟨ cong (λ x → zero * a + x) (sym (inv-+-right (zero * a))) ⟩
    zero * a + (zero * a + inv (zero * a)) ≡⟨ +-assoc (zero * a) (zero * a) (inv (zero * a)) ⟩
    zero * a + zero * a + inv (zero * a)   ≡⟨ cong (λ x → x + inv (zero * a)) (sym (*-dist-+-right a zero zero)) ⟩
    (zero + zero) * a + inv (zero * a)     ≡⟨ cong (λ x → x * a + inv (zero * a)) (zero-+-id-left zero) ⟩
    zero * a + inv (zero * a)              ≡⟨ inv-+-right (zero * a) ⟩
    zero
    ∎

  -1*a+a-is-zero : (a : A) → inv one * a + a ≡ zero 
  -1*a+a-is-zero a = begin
    inv one * a + a              ≡⟨ cong (λ x → inv one * a + x) (sym (one-*-id-left a)) ⟩
    inv one * a + one * a        ≡⟨ sym (*-dist-+-right a (inv one) one) ⟩
    (inv one + one) * a          ≡⟨ cong (λ x → x * a) (inv-+-left one) ⟩
    zero * a                     ≡⟨ zero*a-zero a  ⟩
    zero
    ∎

  *-inv-one-inv : (a : A) → inv one * a ≡ inv a
  *-inv-one-inv a = +-unique-inv a (inv one * a) (-1*a+a-is-zero a)

  x^3-1-eq : (x : A) → (x + inv one) * (x * x + x + one) ≡ (x * x * x) + (inv one) 
  x^3-1-eq x = begin
    (x + inv one) * (x * x + x + one)
      ≡⟨ *-dist-+-right _ _ _ ⟩
    x * (x * x + x + one) + inv one * (x * x + x + one) 
      ≡⟨ cong (λ y → y + (inv one * (x * x + x + one))) (*-dist-+-left x (x * x + x) one) ⟩
    x * (x * x + x) + x * one + inv one * (x * x + x + one)
      ≡⟨ cong (λ y → y + x * one + inv one * (x * x + x + one)) (*-dist-+-left x (x * x) x) ⟩
    x * (x * x) + x * x + x * one + inv one * (x * x + x + one)
      ≡⟨ cong (λ y → y + x * x + x * one + inv one * (x * x + x + one)) (*-assoc x x x) ⟩
    x * x * x + x * x + x * one + inv one * (x * x + x + one)
      ≡⟨ cong (λ y → x * x * x + x * x + y + inv one * (x * x + x + one)) (one-*-id-right x) ⟩
    x * x * x + x * x + x + inv one * (x * x + x + one)
      ≡⟨ cong (λ y → x * x * x + x * x + x + y) (*-dist-+-left (inv one) (x * x + x) one) ⟩
    x * x * x + x * x + x + (inv one * (x * x + x) + inv one * one)
     ≡⟨ cong (λ y → x * x * x + x * x + x + (inv one * (x * x + x) + y)) (one-*-id-right (inv one)) ⟩
    x * x * x + x * x + x + (inv one * (x * x + x) + inv one)
      ≡⟨ cong (λ y → x * x * x + x * x + x + (y + inv one)) (*-dist-+-left (inv one) (x * x) x) ⟩
    x * x * x + x * x + x + (inv one * (x * x) + inv one * x + inv one)
      ≡⟨ cong (λ y → x * x * x + x * x + x + (y + inv one * x + inv one)) (*-inv-one-inv (x * x)) ⟩
    x * x * x + x * x + x + (inv (x * x) + inv one * x + inv one)
      ≡⟨ cong (λ y → x * x * x + x * x + x + (inv (x * x) + y + inv one)) (*-inv-one-inv x) ⟩
    x * x * x + x * x + x + (inv (x * x) + inv x + inv one)
      ≡⟨ cong (λ y → x * x * x + x * x + x + (y + inv one)) (+-comm (inv (x * x)) (inv x)) ⟩
    x * x * x + x * x + x + (inv x + inv (x * x) + inv one)
      ≡⟨ sym (+-assoc (x * x * x + x * x) x ((inv x + inv (x * x) + inv one))) ⟩
    x * x * x + x * x + (x + (inv x + inv (x * x) + inv one))
      ≡⟨ cong (λ y → x * x * x + x * x + (x + y)) (sym (+-assoc (inv x) (inv (x * x)) (inv one))) ⟩
    x * x * x + x * x + (x + (inv x + (inv (x * x) + inv one)))
      ≡⟨ cong (λ y → x * x * x + x * x + y) (+-assoc x (inv x) (inv (x * x) + inv one)) ⟩
    x * x * x + x * x + (x + inv x + (inv (x * x) + inv one))
      ≡⟨ cong (λ y → x * x * x + x * x + (y + (inv (x * x) + inv one))) (inv-+-right x) ⟩
    x * x * x + x * x + (zero + (inv (x * x) + inv one))  
      ≡⟨ cong (λ y → x * x * x + x * x + y) (zero-+-id-left (inv (x * x) + inv one)) ⟩
    x * x * x + x * x + (inv (x * x) + inv one)
      ≡⟨ sym (+-assoc (x * x * x) (x * x) (inv (x * x) + inv one)) ⟩
    x * x * x + (x * x + (inv (x * x) + inv one))
      ≡⟨ cong (λ y → x * x * x + y) (+-assoc (x * x) (inv (x * x)) (inv one)) ⟩
    x * x * x + (x * x + inv (x * x) + inv one)
      ≡⟨ cong (λ y → x * x * x + (y + inv one)) (inv-+-right (x * x)) ⟩
    x * x * x + (zero + inv one)
      ≡⟨ cong (λ y → x * x * x + y) (zero-+-id-left (inv one)) ⟩
    x * x * x + inv one 
    ∎