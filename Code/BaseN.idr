module Basen

import Data.Fin
%access public export

--Defines a data type Base that behaves like a list
data Base: (n: Nat) -> Type where
  Ones: (Fin n) -> Base n
  Next: (Fin n) -> (Base n) -> (Base n)

--Auxiliary function that reverses a Base (S n) onto anpther given Base (S n)
Revonto: (n: Nat) -> (Base (S n)) -> (Base (S n)) -> (Base (S n))
Revonto n accum (Ones x) = Next x accum
Revonto n accum (Next x y) = Revonto n (Next x accum) y

--Reverses a Base (S n)
Rev: (n: Nat) -> (Base (S n)) -> (Base (S n))
Rev n (Ones x) = Ones x
Rev n (Next x y) = Revonto n (Ones x) y

concat: (n: Nat) -> (Base (S n)) -> (Base (S n)) -> (Base (S n))
concat n (Ones x) y = Next x y
concat n (Next x z) y = Next x (concat n z y)

--Fin to Nat
tonatFin: (n: Nat) -> Fin(n) -> Nat
tonatFin (S k) FZ = Z
tonatFin (S k) (FS x) = S (tonatFin k x)

--List Fin to Nat
tonat: (n: Nat) -> Base (S n) -> Nat
tonat n (Ones FZ) = Z
tonat Z (Ones (FS x)) impossible
tonat (S k) (Ones (FS x)) = S(tonat k (Ones x))
tonat n (Next x y) = (tonat n (Ones x)) + (tonat n y)


--Euclid's div
Eucl: (a: Nat) -> (b: Nat) -> (Nat, Nat)
Eucl Z b = (0,0)
Eucl a Z = (0, a)
Eucl (S k) b = case (lte (S (S k)) b) of
                    False => (S(fst(Eucl (minus (S k) b) b)), snd(Eucl (minus (S k) b) b))
                    True => (0, S k)

--Nat to Fin (modular values)
tofinNat: (a: Nat) -> (n: Nat) -> Fin n
tofinNat Z (S j) = FZ
tofinNat (S k) (S j) = case lte (S k) (S j) of
                True => FS (tofinNat k j)
                False =>  (tofinNat (snd(Eucl (S k) (S j))) (S j))

strp: (Base (S n)) -> (Base (S n))
strp (Ones x) = (Ones x)
strp (Next x y) = case x of
                  FZ => strp(y)
                  FS z => Next x y

-- Nat to List Fin n (base n representation)
tofin: Nat -> (n: Nat) -> Base (S n)
tofin Z n = Ones FZ
tofin (S k) n = strp(concat n (tofin q n) (Ones rem)) where
                    rem: Fin (S n)
                    rem = tofinNat (snd(Eucl (S k) (S n))) (S n)
                    q: Nat
                    q = fst(Eucl (S k) (S n))

--embedding Fin n in Fin S n vertically
embn: (n: Nat) -> Fin n -> Fin (S n)
embn (S k) FZ = FZ
embn (S k) (FS x) = FS (embn k x)

--Generates n in (Fin (S n))
Genn: (n: Nat) -> (Fin (S n))
Genn Z = FZ
Genn (S k) = FS (Genn k)

--Checks if a given element of Fin (S n) is in fact n
Isn: (n: Nat) -> (p: Fin (S n)) -> Bool
Isn Z x = True
Isn (S k) FZ = False
Isn (S k) (FS x) = Isn k x

--Proves that the definitional equality for Isn holds
IsnisIsn: (n: Nat) -> (p: Fin (S n)) -> (Isn (S n) (FS p)) = (Isn n p)
IsnisIsn n p = Refl

--Proves that if a given (FS x) is not n in (Fin (S n)), then x is not n-1 in (Fin n)
IsNotnPf:  (n: Nat) -> (p: Fin (S n)) ->  ((Isn (S n) (FS p)) = False) -> ((Isn n p) = False)
IsNotnPf Z _ Refl impossible
IsNotnPf (S k) FZ prf = Refl
IsNotnPf (S k) (FS x) prf = trans (sym (IsnisIsn (S k) (FS x))) prf

--Gives a back embedding whenever the value is not Genn
Predec: (n: Nat) -> (p: Fin (S n)) -> ((Isn n p) = False) -> (Fin n)
Predec Z _ Refl impossible
Predec (S k) FZ Refl = FZ
Predec (S k) (FS x) prf = FS (Predec k x (IsNotnPf (S k) (FS x) prf))

--A type in some sense resembling the decidable type for truth of Isn (with contra replaced by equality to False)
DecIsn: (n: Nat) -> (p: (Fin (S n))) -> Either (Isn n p = True) (Isn n p = False)
DecIsn Z p = Left Refl
DecIsn (S k) FZ = Right Refl
DecIsn (S k) (FS x) = case (DecIsn k x) of
                        Left l => Left (trans (IsnisIsn k x) l)
                        Right r => Right (trans (IsnisIsn k x) r)

--adding two Fin n's
addfin: (n: Nat) -> Fin (S n) -> Fin (S n) -> (Fin (S n), Fin (S n))
addfin Z x y = (FZ,  FZ)
addfin (S k) FZ y = (FZ, y)
addfin (S k) (FS x) y = let
                    a = Genn (S k)
                    b = the (Fin (S (S k))) FZ
                    c = the (Fin (S k)) FZ
                    w = fst(addfin (S k) (embn (S k) x) y)
                    z = snd(addfin (S k) (embn (S k) x) y)
                    in
                    case (DecIsn (S k) z) of
                             Left l => (FS c, b)
                             Right r => (w, FS(Predec (S k) z r))

--adding two reversed lists as specified
addfinl: (n: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
addfinl n (Ones x) (Ones y) = case (addfin n x y) of
                              (FZ, a) => Ones a
                              (FS c, a) => Next a (Ones (FS c))
addfinl n (Ones x) (Next y z) = Next (snd (addfin n x y)) (addfinl n (Ones (fst (addfin n x y))) z)
addfinl n (Next x z) (Ones y) = Next (snd (addfin n x y)) (addfinl n (Ones (fst (addfin n x y))) z)
addfinl n (Next x z) (Next y w) = Next (snd (addfin n x y)) (addfinl n (Ones (fst (addfin n x y))) (addfinl n z w))

--adding two lists
addfinlist: (n: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
addfinlist n xs ys = (Rev n (addfinl n (Rev n xs) (Rev n ys)))

--multiply two reversed lists in Fin S n
mulfinl: (n: Nat) -> Base (S n) -> Base (S n) -> Base (S n)
mulfinl n (Ones FZ) y = Ones FZ
mulfinl n (Ones (FS x)) y = addfinl n y (mulfinl n (Ones (embn n x)) y)
mulfinl n (Next FZ z) y = Next FZ (mulfinl n z y)
mulfinl n (Next (FS x) z) y = addfinl n y (mulfinl n (Next (embn n x) z) y)


--multiply two lists
mulfinList: (n: Nat) -> (Base (S n)) -> (Base (S n)) -> (Base (S n))
mulfinList n xs ys = Rev n (mulfinl n (Rev n xs) (Rev n ys))
