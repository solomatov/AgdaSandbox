module Sort where
  
open import Data.List
open import Data.Nat
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

data Sorted : (l : List ℕ) → Set where
  empty : Sorted []
  singleton : (n : ℕ) → Sorted (n ∷ [])
  cons : (n m : ℕ) → (t : List ℕ) → Sorted (m ∷ t) → n ≤ m → Sorted (n ∷ m ∷ t)

merge : List ℕ → List ℕ → List ℕ
merge [] l = l
merge l [] = l
merge (h1 ∷ t1) (h2 ∷ t2) with (compare h1 h2)
merge (h1 ∷ t1) (.(suc (h1 + k)) ∷ t2) | less .h1 k = h1 ∷ (merge t1 ((h1 + k) ∷ t2))
merge (.h2 ∷ t1) (h2 ∷ t2) | equal .h2 = h2 ∷ h2 ∷ (merge t1 t2)
merge (.(suc (h2 + k)) ∷ t1) (h2 ∷ t2) | greater .h2 k = h2 ∷ (merge ((h2 + k) ∷ t1) t2)

