{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CP(check_conj) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Nat = Zero_nat | Suc Nat;

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) = (case n of {
                    Zero_nat -> x : xs;
                    Suc m -> drop m xs;
                  });

last :: forall a. [a] -> a;
last (x : xs) = (if null xs then x else last xs);

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) = (case n of {
                    Zero_nat -> [];
                    Suc m -> x : take m xs;
                  });

iter :: forall a. Nat -> (a -> a) -> a -> a;
iter Zero_nat f = (\ x -> x);
iter (Suc n) f = (\ x -> f (iter n f x));

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;

one_nat :: Nat;
one_nat = Suc Zero_nat;

inverse :: forall a b. ((a, b), Bool) -> ((a, b), Bool);
inverse (x, True) = (x, False);
inverse (x, False) = (x, True);

uncycle :: forall a b. (Eq a, Eq b) => [((a, b), Bool)] -> [((a, b), Bool)];
uncycle [] = [];
uncycle [x] = [x];
uncycle (x : v : va) =
  (if x == inverse (last (v : va))
    then uncycle (take (minus_nat (size_list (v : va)) one_nat) (v : va))
    else x : v : va);

cycle_at_i :: forall a b. [((a, b), Bool)] -> Nat -> [((a, b), Bool)];
cycle_at_i x i = drop i x ++ take i x;

checkcycleeq ::
  forall a b.
    (Eq a, Eq b) => Nat -> [((a, b), Bool)] -> [((a, b), Bool)] -> Bool;
checkcycleeq (Suc n) x y = cycle_at_i x (Suc n) == y || checkcycleeq n x y;
checkcycleeq Zero_nat x y = cycle_at_i x Zero_nat == y;

ccyclicp ::
  forall a b. (Eq a, Eq b) => [((a, b), Bool)] -> [((a, b), Bool)] -> Bool;
ccyclicp x y = checkcycleeq (size_list x) x y;

reduct :: forall a b. (Eq a, Eq b) => [((a, b), Bool)] -> [((a, b), Bool)];
reduct [] = [];
reduct [x] = [x];
reduct (g1 : g2 : wrd) =
  (if g1 == inverse g2 then wrd else g1 : reduct (g2 : wrd));

cyclic_reduct ::
  forall a b. (Eq a, Eq b) => [((a, b), Bool)] -> [((a, b), Bool)];
cyclic_reduct xs = uncycle (iter (size_list xs) reduct xs);

check_conj ::
  forall a b. (Eq a, Eq b) => [((a, b), Bool)] -> [((a, b), Bool)] -> Bool;
check_conj a b = ccyclicp (cyclic_reduct a) (cyclic_reduct b);

}
