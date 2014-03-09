module WF where

open import Data.Nat
open import Data.Nat.Properties


trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z 
trans z≤n y<=z = z≤n
trans (s≤s x<=y) (s≤s y<=z) = s≤s (trans x<=y y<=z)

data Acc (n : ℕ) : Set where
  acc : ((m : ℕ) → (m < n) → Acc m) → Acc n

<-wf : (n : ℕ) → Acc n 
<-wf zero = acc (λ m ())
<-wf (suc n) = acc af
  where
    af : (m : ℕ) → m < (suc n) → Acc m
    af zero zero<sn = acc λ k ()
    af (suc m) (s≤s m<n) with <-wf n
    ... | (acc afn) = acc (λ k k<m → afn k (trans k<m m<n))





