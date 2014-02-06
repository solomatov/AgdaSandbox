module ViewsSandbox where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Unit
open import Function
open import Level

open ≡-Reasoning

data False : Set where
record True : Set where


satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = T (p x)

infixr 30 _:all:_
data All {A : Set} (P : A → Set) : List A → Set where
  all[]   : All P []
  _:all:_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Find {A : Set} (p : A → Bool) : List A → Set where
  found :     (xs : List A) (y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : {xs : List A}         → All (satisfies (not ∘ p)) xs   → Find p xs

true-is-true : {b : Bool} → b ≡ true → T b
true-is-true refl = tt

false-is-false : {b : Bool} → b ≡ false → T (not b)
false-is-false refl = tt

find : {A : Set} (p : A → Bool) (xs : List A) → Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with p x | inspect p x
... | true  | Reveal_is_.[ eq ] = found [] x (true-is-true eq) xs
... | false | Reveal_is_.[ eq ] with find p xs
... | not-found rest = not-found (false-is-false eq :all: rest)
find p (x₁ ∷ .(xs ++ y ∷ ys)) | false | Reveal_is_.[ eq ] | found xs y x ys = found (x₁ ∷ xs) y x ys 
