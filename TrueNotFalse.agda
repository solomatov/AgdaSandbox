module TrueNotFalse where

open import Level

data False : Set where

abort : {T : Set} → False → T
abort ()

data True : Set where
  tt : True

not : Set → Set
not A = A → False

data Bool : Set where
  true : Bool
  false : Bool

bool-ind : {M : Bool → Set} → M true → M false → (b : Bool) → M b
bool-ind {M} mt mf true = mt
bool-ind {M} mt mf false = mf

if_then_else : {A : Set} →  Bool → A → A → A
if true then ifTrue else _ = ifTrue
if false then _ else ifFalse = ifFalse

data _eq_  {l : Level} {A : Set l} : A → A → Set l where
  refl : {a : A} → a eq a 

eq-ind : {l : Level} {A : Set l} → (M : A → A → Set) → (a b : A) → (a eq b) → (M a a) → M a b
eq-ind M a .a refl Maa = Maa

cong : {A : Set} {B : Set₁} {a₁ a₂ : A} → (f : A → B) → a₁ eq a₂ → f a₁ eq f a₂
cong f refl = refl

false-is-true-false : False eq True → False
false-is-true-false false-true = eq-ind (λ a b → (b → b → False)) False True false-true (λ f1 f2 → f1) tt tt

bool-to-type : Bool → Set
bool-to-type true = True
bool-to-type false = False

true-not-false : not (false eq true)
true-not-false eq = false-is-true-false (cong bool-to-type eq ) 

