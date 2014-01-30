module NatProps where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function
open import Monoid

open ≡-Reasoning

+one : (n : ℕ) → 1 + n ≡ n + 1
+one zero = refl
+one (suc n) = cong suc (+one n) 

zero-+id-right : (n : ℕ) → n + zero ≡ n
zero-+id-right zero = refl
zero-+id-right (suc n) = cong suc (zero-+id-right n) 

zero-+id-left : (n : ℕ) → zero + n ≡ n
zero-+id-left n = refl

succMN : (n m : ℕ) → suc n + m ≡ n + suc m
succMN zero m = refl
succMN (suc n) m = begin
  suc (suc n) + m      ≡⟨ refl ⟩
  suc (suc n + m)      ≡⟨ cong suc (succMN n m) ⟩
  suc (n + suc m)      ≡⟨ refl ⟩
  suc n + suc m
  ∎

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero m = begin 
  zero + m          ≡⟨ zero-+id-left _ ⟩
  m                 ≡⟨ sym (zero-+id-right _) ⟩
  m + zero 
  ∎  
+-comm (suc n) m = begin 
  (suc n) + m       ≡⟨ refl ⟩ 
  suc (n + m)       ≡⟨ cong suc (+-comm n m) ⟩
  suc (m + n)       ≡⟨ refl ⟩
  suc m + n ≡⟨ succMN m n  ⟩
  m + (suc n)
  ∎

+-assoc : (n m k : ℕ) → (n + m) + k ≡ n + (m + k)
+-assoc zero m k = refl
+-assoc (suc n) m k = begin
  suc n + m + k ≡⟨ refl ⟩
  suc (n + m + k) ≡⟨ cong suc (+-assoc n m k) ⟩
  suc (n + (m + k)) ≡⟨ refl ⟩
  suc n + (m + k)
  ∎

ℕ-monoid : Monoid ℕ
ℕ-monoid = record {
      _+_ = _+_ 
    ; zero = zero  
    ; zero-+id-left = zero-+id-left
    ; zero-+id-right = zero-+id-right
    ; +-assoc = +-assoc 
  }

open MonoidProperties ℕ ℕ-monoid

+-unique-inv-ℕ : (a ia₁ ia₂ : ℕ) → (ia₁ + a ≡ zero) → (a + ia₂ ≡ zero) → (ia₁ ≡ ia₂)
+-unique-inv-ℕ = +-unique-inv
