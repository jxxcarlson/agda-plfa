-- ℕ

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

double : ℕ → ℕ
double zero = zero
double (suc m) = suc (suc (double m))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst)

-- BIN

data Bin : Set where
  <> : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- CONVERSIONS

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

-- TEST:

-- map (λ x → (from (to x))) (range 10)
-- 10 ∷ 9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []

-- PROOF:  from . left  = id

-- First, three lemmas

le-to-suc : ∀ (n : ℕ) → to(suc n) ≡ inc(to n)
le-to-suc n = refl

le-from-inc : ∀ ( b : Bin ) → from(inc b) ≡ suc(from b)
le-from-inc <> = refl
le-from-inc (b O)  = refl
le-from-inc(b I) rewrite le-from-inc b = refl

le-from-inc-to : ∀ (n : ℕ) → from(inc(to n)) ≡ suc(from(to n))
le-from-inc-to n =   le-from-inc(to n)

-- Then the proposition and its proof

id-from-to : ∀ (n : ℕ) → from(to n) ≡ n
id-from-to 0 = refl
id-from-to (suc n) rewrite le-to-suc n | le-from-inc-to n | cong suc (id-from-to n) = refl




 
