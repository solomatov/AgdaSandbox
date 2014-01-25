module Ring where

open import Data.Bool
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function

infixl 0 _≡-t_
_≡-t_ : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_≡-t_ refl refl = refl

≡-s : {A : Set} → {a b : A} → a ≡ b → b ≡ a
≡-s refl = refl


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
  +-unique-inv a ia eq = 
    (≡-s (zero-+-id-right ia)) ≡-t
    cong (λ x → ia + x) (≡-s (inv-+-right a)) ≡-t
    +-assoc ia a (inv a) ≡-t
    cong (λ x → x + inv a) eq ≡-t
    zero-+-id-left (inv a)

  zero*a-zero : (a : A) → zero * a ≡ zero
  zero*a-zero a = 
    ≡-s (zero-+-id-right (zero * a)) ≡-t 
    cong (λ x → zero * a + x) (≡-s (inv-+-right (zero * a))) ≡-t
    +-assoc (zero * a) (zero * a) (inv (zero * a)) ≡-t 
    cong (λ x → x + inv (zero * a)) (≡-s (*-dist-+-right a zero zero)) ≡-t
    cong (λ x → x * a + inv (zero * a)) (zero-+-id-left zero) ≡-t
    inv-+-right (zero * a)

  -1*a+a-is-zero : (a : A) → inv one * a + a ≡ zero 
  -1*a+a-is-zero a =  
    cong (λ x → inv one * a + x) (≡-s (one-*-id-left a)) ≡-t
    ≡-s (*-dist-+-right a (inv one) one) ≡-t    
    cong (λ x → x * a) (inv-+-left one) ≡-t
    zero*a-zero a 

  *-inv-one-inv : (a : A) → inv one * a ≡ inv a
  *-inv-one-inv a = +-unique-inv a (inv one * a) (-1*a+a-is-zero a)

  x^3-1-eq : (x : A) → (x + inv one) * (x * x + x + one) ≡ (x * x * x) + (inv one) 
  x^3-1-eq x = 
    *-dist-+-right (x * x + x + one) x (inv one) ≡-t  
    cong (λ y → y + (inv one * (x * x + x + one))) (*-dist-+-left x (x * x + x) one) ≡-t 
    cong (λ y → y + x * one + inv one * (x * x + x + one)) (*-dist-+-left x (x * x) x) ≡-t
    cong (λ y → y + x * x + x * one + inv one * (x * x + x + one)) (*-assoc x x x) ≡-t
    cong (λ y → x * x * x + x * x + y + inv one * (x * x + x + one)) (one-*-id-right x) ≡-t
    cong (λ y → x * x * x + x * x + x + y) (*-dist-+-left (inv one) (x * x + x) one) ≡-t 
    cong (λ y → x * x * x + x * x + x + (inv one * (x * x + x) + y)) (one-*-id-right (inv one)) ≡-t
    cong (λ y → x * x * x + x * x + x + (y + inv one)) (*-dist-+-left (inv one) (x * x) x) ≡-t 
    cong (λ y → x * x * x + x * x + x + (y + inv one * x + inv one)) (*-inv-one-inv (x * x)) ≡-t 
    cong (λ y → x * x * x + x * x + x + (inv (x * x) + y + inv one)) (*-inv-one-inv x) ≡-t
    cong (λ y → x * x * x + x * x + x + (y + inv one)) (+-comm (inv (x * x)) (inv x)) ≡-t 
    ≡-s (+-assoc (x * x * x + x * x) x ((inv x + inv (x * x) + inv one))) ≡-t
    cong (λ y → x * x * x + x * x + (x + y)) (≡-s (+-assoc (inv x) (inv (x * x)) (inv one))) ≡-t
    cong (λ y → x * x * x + x * x + y) (+-assoc x (inv x) (inv (x * x) + inv one)) ≡-t
    cong (λ y → x * x * x + x * x + (y + (inv (x * x) + inv one))) (inv-+-right x) ≡-t
    cong (λ y → x * x * x + x * x + y) (zero-+-id-left (inv (x * x) + inv one)) ≡-t
    ≡-s (+-assoc (x * x * x) (x * x) (inv (x * x) + inv one)) ≡-t
    cong (λ y → x * x * x + y) (+-assoc (x * x) (inv (x * x)) (inv one)) ≡-t
    cong (λ y → x * x * x + (y + inv one)) (inv-+-right (x * x)) ≡-t
    cong (λ y → x * x * x + y) (zero-+-id-left (inv one))