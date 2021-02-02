-- NAT

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

--- LIST

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

range : ℕ → List ℕ
range 0 = 0 ∷ []
range (suc n) = (suc n) ∷ range n

map : ∀ {A : Set} → (A → A) → List A → List A
map f [] = []
map f (x ∷ xs) = (f x) ∷ map f xs

-- ℕ

double : ℕ → ℕ
double 0 = 0
double (suc m) = suc (suc (double m))

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)


-- BIN


data Bin : Set where
  <> : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc <> = <> I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to 0 = <> O
to (suc n) = inc (to n)

from : Bin → ℕ
from <> = 0
from (x O) = double (from x)
from (x I) = suc (double  (from x))

-- ℕ LEMMAS

le-double : ∀ (n : ℕ) → double(suc n) ≡ suc(suc(double n))
le-double n = refl

le-to-suc : ∀ (n : ℕ) → to(suc n) ≡ inc(to n)
le-to-suc n = refl

-- BIN LEMMAS

le-from-shift : ∀ (b : Bin) → from (b O) ≡ double (from b)
le-from-shift <> = refl
le-from-shift (b O) = refl
le-from-shift (b I) = refl

le-from-shift2 : ∀ (b : Bin) → from (b I) ≡ suc (double (from b))
le-from-shift2 <> = refl
le-from-shift2 (b O) = refl
le-from-shift2 (b I) = refl

-- LEMMAS WITH REWRITE

le-from-inc : ∀ ( b : Bin ) → from(inc b) ≡ suc(from b)
le-from-inc <> = refl
le-from-inc (b O)  = refl
le-from-inc(b I) rewrite le-from-inc b = refl


le-from-inc-to : ∀ (n : ℕ) → from(inc(to n)) ≡ suc(from(to n))
le-from-inc-to n =   le-from-inc(to n)

fix : Bin → Bin
fix <> = <> O
fix b = b

-- TEST

-- map (λ x → (from (to x))) (range 10)
-- 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []


-- BIN PROPOSITIONS

id-from-to : ∀ (n : ℕ) → from(to n) ≡ n
id-from-to 0 = refl
id-from-to (suc n) rewrite le-to-suc n | le-from-inc-to n | cong suc (id-from-to n) = refl




 
