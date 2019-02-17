module Primes

import NatUtils

%access public export
%default total

--isDivisible a b can be constucted if b divides a
isDivisible : Nat -> Nat -> Type
isDivisible a b = (n : Nat ** (GT n 0, a = b * n))

--1 divides everything
oneDiv : (a : Nat) -> {auto x : GT a 0} -> isDivisible a 1
oneDiv a {x=pf} = (a ** (pf , rewrite plusZeroRightNeutral a in Refl))

--If 1|a => 1*c | a*c
mulDiv : (a, c : Nat) -> {auto pf1 : GT a 0} -> {auto pf2 : GT c 0} ->
  isDivisible a 1 -> isDivisible (a * c) c
mulDiv a c {pf1=p} x = (a ** (p ,rewrite multCommutative a c in Refl))

--Prime Type
Prime : (p : Nat) -> {auto prf : LTE 2 p} -> Type
Prime p = ((a : Nat , b : Nat) -> (p = a*b , Either (a=1) (b=1)))

--Either(a=b)(_) <=> Either (S a = S b)(_)
help1 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT (S a) (S b)) (LT (S b) (S a))) ->
  Either (S a = S b) (Either (LT (S a) (S b)) (LT (S b) (S a)))
help1 {a} {b} (Left l) = Left (eqSucc a b l)
help1 (Right r) = Right r

--Either(_)(Either(Sa<Sb)(_)) <=> Either (_)(Either(a<b)(_))
help2 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT a b) (LT (S b) (S a))) ->
  Either (a = b) (Either (LT (S a) (S b)) (LT (S b) (S a)))
help2 (Left l) = Left l
help2 {a} {b} (Right (Left l)) = Right(Left (LTESucc l))
help2 (Right (Right r)) = Right (Right r)

--Either(_)(Either(_)(Sb<Sa)) <=> Either (_)(Either(_)(b<a))
help3 : {a : Nat} -> {b : Nat} ->
  Either (a = b) (Either (LT a b) (LT b a)) ->
  Either (a = b) (Either (LT a b) (LT (S b) (S a)))
help3 (Left l) = Left l
help3 (Right (Left l)) = Right(Left l)
help3 {a} {b} (Right (Right r)) = Right (Right (LTESucc r))

|||Either a = b, a < b, or a > b
totOrdNat : (a : Nat) -> (b : Nat) ->
  Either (a = b) (Either (LT a b) (LT b a))
totOrdNat Z Z = Left Refl
totOrdNat Z (S k) = Right (Left (LTESucc LTEZero))
totOrdNat (S k) Z = Right (Right (LTESucc LTEZero))
totOrdNat (S k) (S j) = help1 (help2 (help3 (totOrdNat k j)))

--LTE a b => LTE a*n b*n
multRightLTE : (a,b : Nat) -> (n : Nat) -> GT n 0 ->
  LTE a b -> LTE (a*n) (b*n)
multRightLTE a b (S Z) (LTESucc LTEZero) lteab =
                            rewrite multOneRightNeutral a in
                            rewrite multOneRightNeutral b in
                            lteab
multRightLTE a b (S (S k)) (LTESucc LTEZero{right=(S k)}) lteab =
          rewrite multRightSuccPlus a (S k) in
          rewrite multRightSuccPlus b (S k) in
          lteSumIsLte a b (mult a (S k)) (mult b (S k)) lteab
          (multRightLTE a b (S k) (LTESucc LTEZero{right=k}) lteab)

--If a = b*n, b <= a
aEqProdImpAGtB : (a,b,n : Nat) -> GT n 0 -> (a = b*n) -> LTE b a
aEqProdImpAGtB _ _ Z LTEZero _ impossible
aEqProdImpAGtB _ _ Z (LTESucc _) _ impossible
aEqProdImpAGtB (b * (S k)) b (S k) x Refl = case b of
              Z => LTEZero
              (S m) =>
                rewrite sym (multOneLeftNeutral (S m)) in
                rewrite multCommutative (S m) (S k) in
                rewrite multDistributesOverPlusRight k (S Z) m in
                rewrite plusCommutative (k*1) (k*m) in
                rewrite plusAssociative m (k*m) (k*1) in
                rewrite plusCommutative (m + k*m) (k*1) in
                rewrite sym (multDistributesOverPlusRight (S k) 1 m) in
                multRightLTE 1 (S k) (S m) (LTESucc (LTEZero)) x

--Not LTE implies GT
--(this is from a pull request on Idris-lang which was not accepted)
notLTEImpliesGT : Not (LTE i j) -> GT i j
notLTEImpliesGT {i = Z}             notLt = absurd $ notLt LTEZero
notLTEImpliesGT {i = S k} {j = Z}   _     = LTESucc LTEZero
notLTEImpliesGT {i = S j} {j = S k} notLt = LTESucc (notLTEImpliesGT (notLt . LTESucc))

--Decidability for divisibility
decDiv : (p : Nat) -> LTE 2 p -> (x : Nat) -> Dec (isDivisible p x)
decDiv Z LTEZero _ impossible
decDiv Z (LTESucc _) _ impossible
decDiv (S Z) (LTESucc LTEZero) _ impossible
decDiv (S Z) (LTESucc (LTESucc _)) _ impossible
decDiv (S (S k)) (LTESucc (LTESucc LTEZero)) x =
            case totOrdNat (S (S k)) x of
                (Left l) => Yes (1 ** ((LTESucc LTEZero),
                                       rewrite l in
                                       rewrite sym (multOneRightNeutral x) in
                                       Refl))
                (Right (Left l)) => No ?e3
                (Right (Right r)) => ?e4

--Spare code
{-
--Type for isPrime. A number p is prime if all numbers dividing
--it are either p or 1. (In the primality checker, I am checking
--for numbers until p, hence the p case is not included. Will
--be changed in a future update.)
isPrime : Nat -> Type
isPrime p = (LTE 2 p ,
            (x : Nat **
            (isDivisible p x , x = 1)))
--Does the job, but is not very useful. Will be replaced later.
checkPrime : (p : Nat) -> LTE 2 p -> {default (p-1) iter : Nat} ->
  Maybe (isPrime p)
checkPrime p pf {iter=Z} = Nothing
checkPrime p pf {iter=(S Z)} = Just (pf, ((S Z) ** (oneDiv p, Refl)))
checkPrime p pf {iter=(S k)} = case modNatNZ p (S k) SIsNotZ of
                            Z => Nothing
                            (S m) => checkPrime p pf {iter=k}
-}
