module Sort where
  
open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function

open ≡-Reasoning

data Sorted (A : Set) (cmp : A → A → Bool) : (l : List A) → Set where
  empty : Sorted A cmp []
  singleton : (a : A) → Sorted A cmp (a ∷ [])

