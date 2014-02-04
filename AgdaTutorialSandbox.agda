module AgdaTutorialSandbox where

open import Relation.Binary.PropositionalEquality
open import Data.Nat

open ≡-Reasoning

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_  : {n : ℕ} → A → Vec A n → Vec A (suc n)

vmap : {A B : Set} {n : ℕ} → Vec A n → (f : A → B) → Vec B n
vmap [] f = []
vmap (x ∷ v) f = (f x) ∷ (vmap v f)

-- Excercise 2.2
Matrix : Set → ℕ → ℕ → Set
Matrix A n m = Vec (Vec A n) m

vec : {n : ℕ} {A : Set} → A → Vec A n
vec {zero} x = []
vec {suc n} x = x ∷ vec x

infixl 90 _$_
_$_ : {n : ℕ} {A B : Set} → Vec (A → B) n → Vec A n → Vec B n
[] $ xs = []
(f ∷ fs) $ (x ∷ xs) = (f x) ∷ fs $ xs

transpose : {A : Set} {n m : ℕ} → Matrix A n m → Matrix A m n
transpose {_} {n} {.zero} [] = vec []
transpose (m ∷ mt) =  vmap m (λ a v → a ∷ v) $ transpose mt