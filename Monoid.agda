module Monoid where

open import Data.Bool
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Function
open ≡-Reasoning

record Monoid (A : Set) : Set where
  infixl 4 _+_
  field
    _+_ : A → A → A
    zero : A
    zero-+id-left : (a : A) → zero + a ≡ a
    zero-+id-right : (a : A) → a + zero ≡ a
    +-assoc : (a b c : A) → (a + b) + c ≡ a + (b + c)


module MonoidProperties (A : Set) (m : Monoid A) where
  open Monoid m

  +-unique-inv : (a ia₁ ia₂ : A) → (ia₁ + a ≡ zero) → (a + ia₂ ≡ zero) → (ia₁ ≡ ia₂)
  +-unique-inv a ia₁ ia₂ eq₁ eq₂ = begin
    ia₁                       ≡⟨ sym (zero-+id-right _) ⟩
    ia₁ + zero                ≡⟨ cong (λ x → ia₁ + x) (sym eq₂) ⟩
    ia₁ + (a + ia₂)           ≡⟨ sym (+-assoc _ _ _)  ⟩
    ia₁ + a + ia₂             ≡⟨ cong (λ x → x + ia₂) eq₁ ⟩
    zero + ia₂                ≡⟨ zero-+id-left _ ⟩
    ia₂
    ∎
