module NatProps where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

+one : (n : ℕ) → 1 + n ≡ n + 1
+one zero = refl
+one (suc n) = cong suc (+one n) 

zero+left-id : (n : ℕ) → n + zero ≡ n
zero+left-id zero = refl
zero+left-id (suc n) = cong suc (zero+left-id n) 

zero+right-id : (n : ℕ) → zero + n ≡ n
zero+right-id n = refl

succMN : (n m : ℕ) → suc n + m ≡ n + suc m
succMN zero m = refl
succMN (suc n) m = begin
  suc (suc n) + m      ≡⟨ refl ⟩
  suc (suc n + m)      ≡⟨ cong suc (succMN n m) ⟩
  suc (n + suc m)      ≡⟨ refl ⟩
  suc n + suc m
  ∎

commPlus : (n m : ℕ) → n + m ≡ m + n
commPlus zero m = begin 
  zero + m          ≡⟨ zero+right-id _ ⟩
  m                 ≡⟨ sym (zero+left-id _) ⟩
  m + zero 
  ∎  
commPlus (suc n) m = begin 
  (suc n) + m       ≡⟨ refl ⟩ 
  suc (n + m)       ≡⟨ cong suc (commPlus n m) ⟩
  suc (m + n)       ≡⟨ refl ⟩
  suc m + n ≡⟨ succMN m n  ⟩
  m + (suc n)
  ∎
