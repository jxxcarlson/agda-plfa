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

psuc : ∀ (n : ℕ) → suc n ≡ n + 1
psuc zero = refl
psuc (suc n) rewrite psuc n = refl

pdouble : ∀ (n : ℕ) → double(suc n) ≡ suc(suc(double n))
pdouble n = refl

pto : ∀ (n : ℕ) → to(suc n) ≡ inc(to n)
pto n = refl

-- BIN LEMMAS

pfromO : ∀ (b : Bin) → from(b O) ≡ double(from b)
pfromO b = refl

pbO : ∀ (b : Bin) → from (b O) ≡ double (from b)
pbO <> = refl
pbO (b O) = refl
pbO (b I) = refl

pbI : ∀ (b : Bin) → from (b I) ≡ suc (double (from b))
pbI <> = refl
pbI (b O) = refl
pbI (b I) = refl

p-from-inc : ∀ ( b : Bin ) → from(inc b) ≡ suc(from b)
p-from-inc <> = refl
p-from-inc (b O)  rewrite pbO b = refl
p-from-inc (b I) rewrite pbI b | pdouble (from b) | p-from-inc b | pdouble (from b) = refl

pfi-n : ∀ (n : ℕ) → from(inc(to n)) ≡ suc(from(to n))
pfi-n n = p-from-inc(to n)

fix : Bin → Bin
fix <> = <> O
fix b = b


-- BIN PROPOSITIONS

id-from-to : ∀ (n : ℕ) → from(to n) ≡ n
id-from-to 0 = refl
id-from-to (suc n) rewrite pto n | pfi-n n | cong suc (id-from-to n) = refl


id-to-from : ∀ (b : Bin) → to(from b) ≡ fix b
id-to-from <> = refl
id-to-from (b O) rewrite pfromO b = {!ind.!}
id-to-from (b I) = {!!}



 
