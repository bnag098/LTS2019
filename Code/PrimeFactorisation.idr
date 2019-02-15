module PrimeFactorisation

import BaseN
%access public export

data Factor: (n : Nat) -> (a: Nat) -> (b: Nat) -> n=a*b -> Type

data Prime: (n:Nat) -> {auto p: LTE (S Z) n} -> Factor n a b pf -> a=1|b=1 -> Type

-- findFact: (n: Nat) ->  ( m:(Nat, Nat) ** (Factor n (fst m) (snd m) pf) )

-- apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
-- apNat f m m Refl = Refl
--
-- EuclidWithProof: (a: Nat) -> (b: Nat) -> (k:(Nat, Nat) ** (a = b*fst(k) + snd(k)))
-- EuclidWithProof Z b = ((Z,Z) ** apNat (\x: Nat => x*b + x) Z Z Refl)
-- EuclidWithProof (S k) b = ?EuclidWithProof_rhs_2


findFact: (n: Nat) -> (Nat, Nat)--** n = (fst m) * (snd m))
findFact Z = ((Z,Z) {-** Refl-})
findFact (S Z) = ((S Z, S Z) {-** Refl-})
findFact (S (S k)) = findFactAux (S(S k)) (S Z) where
  findFactAux: Nat -> Nat-> (Nat, Nat)
  findFactAux k j = if (snd(Eucl k (S j)) == Z) then ((S j), fst(Eucl k (S j)))
    else
      if (lte ((S (S j))*(S (S j))) k) then findFactAux k (S j)
        else (1, k)
