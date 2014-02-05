module AgdaTutorialSandbox where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Function

open ≡-Reasoning

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_  : {n : ℕ} → A → Vec A n → Vec A (suc n)

vmap : {A B : Set} {n : ℕ} → Vec A n → (f : A → B) → Vec B n
vmap [] f = []
vmap (x ∷ v) f = (f x) ∷ (vmap v f)


data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)

_!_ : {n : ℕ} {A : Set} → Vec A n → Fin n → A
[] ! ()
(x ∷ xs) ! fzero = x
(x ∷ xs) ! (fsuc i) = xs ! i

tabulate : {n : ℕ} {A : Set} → (Fin n → A) → Vec A n 
tabulate {zero} f = []
tabulate {suc n} f = (f fzero) ∷ tabulate (f ∘ fsuc)

-- Excercise 2.1
Matrix : Set → ℕ → ℕ → Set
Matrix A n m = Vec (Vec A n) m

vec : {n : ℕ} {A : Set} → A → Vec A n
vec {zero} x = []
vec {suc n} x = x ∷ vec x

infixl 90 _$$_
_$$_ : {n : ℕ} {A B : Set} → Vec (A → B) n → Vec A n → Vec B n
[] $$ xs = []
(f ∷ fs) $$ (x ∷ xs) = (f x) ∷ fs $$ xs

transpose : {A : Set} {n m : ℕ} → Matrix A n m → Matrix A m n
transpose {_} {n} {.zero} [] = vec []
transpose (m ∷ mt) =  vmap m (λ a v → a ∷ v) $$ transpose mt

-- Excercise 2.2
lem-!-tab : {A : Set} {n : ℕ} (f : Fin n → A) (i : Fin n) → (tabulate f) ! i ≡ f i 
lem-!-tab f fzero    = refl
lem-!-tab f (fsuc i) = begin  
  tabulate f ! fsuc i               ≡⟨ refl ⟩
  tabulate (λ x → f (fsuc x)) ! i   ≡⟨ lem-!-tab (f ∘ fsuc) i  ⟩
  f (fsuc i)
  ∎

lem-tab-! : {A : Set} {n : ℕ} (v : Vec A n) → tabulate (_!_ v) ≡ v
lem-tab-! [] = refl
lem-tab-! (x ∷ v) = begin
  tabulate (_!_ (x ∷ v)) ≡⟨ refl ⟩
  x ∷ tabulate (λ y → v ! y) ≡⟨ cong (λ z → x ∷ z) (lem-tab-! v) ⟩
  x ∷ v
  ∎

-- Excercise 2.3
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : {y : A} {xs ys : List A} → xs ⊆ ys → xs       ⊆ (y ∷ ys)
  keep : {x : A} {xs ys : List A} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

⊆-refl : {A : Set} {xs : List A} → xs ⊆ xs
⊆-refl {A} {[]} = stop
⊆-refl {A} {x ∷ xs} = keep ⊆-refl

⊆-empty : {A : Set} {xs : List A} → [] ⊆ xs
⊆-empty {A} {[]} = stop
⊆-empty {A} {x ∷ xs} = drop ⊆-empty

⊆-trans : {A : Set} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans stop ys-zs = ⊆-empty
⊆-trans (drop xs-ys) (drop ys-zs) = drop (⊆-trans (drop xs-ys) ys-zs)
⊆-trans (drop xs-ys) (keep ys-zs) = drop (⊆-trans xs-ys ys-zs)
⊆-trans (keep xs-ys) (drop ys-zs) = drop (⊆-trans (keep xs-ys) ys-zs)
⊆-trans (keep xs-ys) (keep ys-zs) = keep (⊆-trans xs-ys ys-zs)
