module Sort where
  
open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning


plusOne : (n : ℕ) → 1 + n ≡ n + 1
plusOne zero = refl
plusOne (suc n) = cong suc (plusOne n) 

zeroOne : (n : ℕ) → zero + n ≡ n + zero
zeroOne n = {!!}

sucMN : (n m : ℕ) → suc n + m ≡ m + suc n
sucMN n m = {!!}

commPlus : (n m : ℕ) → n + m ≡ m + n
commPlus zero m = zeroOne m
commPlus (suc n) m = {!!}

-- declare semi group. show that Nat is semigroup. and show some fact which is implied for Naat because it's semigroup