{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module WP(Nat, normal_form) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Nat = Zero_nat | Suc Nat;

funpow :: forall a. Nat -> (a -> a) -> a -> a;
funpow Zero_nat f = id;
funpow (Suc n) f = f . funpow n f;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

inverse :: forall a b. ((a, b), Bool) -> ((a, b), Bool);
inverse (x, True) = (x, False);
inverse (x, False) = (x, True);

reduce :: forall a b. (Eq a, Eq b) => [((a, b), Bool)] -> [((a, b), Bool)];
reduce [] = [];
reduce [x] = [x];
reduce (g1 : g2 : wrd) =
  (if g1 == inverse g2 then wrd else g1 : reduce (g2 : wrd));

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

normal_form :: forall a b. (Eq a, Eq b) => [((a, b), Bool)] -> [((a, b), Bool)];
normal_form w = funpow (size_list w) reduce w;

}
