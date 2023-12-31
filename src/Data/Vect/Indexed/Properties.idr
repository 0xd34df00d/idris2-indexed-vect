module Data.Vect.Indexed.Properties

import Data.Vect
import Data.Vect.Indexed
import Data.Vect.Indexed.Helpers

%default total

export
mapFusion : {0 tyf0 : _} ->
            (f1 : tyf0 ~> tyf1) ->
            (f2 : tyf1 ~> tyf2) ->
            (vec : IVect n tyf0) ->
            map f2 (map f1 vec) = map (f2 . f1) vec
mapFusion f1 f2 [] = Refl
mapFusion f1 f2 (x :: xs) = rewrite mapFusion (\y => f1 y) (\y => f2 y) xs in Refl

export
mapId : (vec : IVect n tyf) ->
        map (\x => x) vec = vec
mapId [] = Refl
mapId (x :: xs) = rewrite mapId xs in Refl

export
mapTabulate : {n : Nat} ->
              {0 tyf, tyf' : _} ->
              (tf : (idx : Fin n) -> tyf idx) ->
              (mf : tyf ~> tyf') ->
              map mf (tabulate tf) = tabulate (\idx => mf (tf idx))
mapTabulate {n = Z} tf mf = Refl
mapTabulate {n = S n} tf mf = rewrite mapTabulate {n} (\idx => tf (FS idx)) (\y => mf y) in Refl

export
fromVectToVectId : (xs : Vect n a) ->
                   toVect (\a' => a') (fromVect xs) = xs
fromVectToVectId [] = Refl
fromVectToVectId (x :: xs) = rewrite fromVectToVectId xs in Refl

export
unzipZipId : (xs : IVect n tyf0) ->
             (ys : IVect n tyf1) ->
             unzip (zip xs ys) = (xs, ys)
unzipZipId [] [] = Refl
unzipZipId (x :: xs) (y :: ys) = rewrite unzipZipId xs ys in Refl

export
zipUnzipId : (xs : IVect n (zipTyF tyf0 tyf1)) ->
             zip' (unzip xs) = xs
zipUnzipId [] = Refl
zipUnzipId ((_, _) :: xs) with (zipUnzipId xs) | (unzip xs)
  _ | rec | (_, _) = rewrite rec in Refl

export
unzip3Zip3Id : (xs : IVect n tyf0) ->
               (ys : IVect n tyf1) ->
               (zs : IVect n tyf2) ->
               unzip3 (zip3 xs ys zs) = (xs, ys, zs)
unzip3Zip3Id [] [] [] = Refl
unzip3Zip3Id (x :: xs) (y :: ys) (z :: zs) = rewrite unzip3Zip3Id xs ys zs in Refl

export
zip3Unzip3Id : (xs : IVect n (zip3TyF tyf0 tyf1 tyf2)) ->
               zip3' (unzip3 xs) = xs
zip3Unzip3Id [] = Refl
zip3Unzip3Id ((_, _, _) :: xs) with (zip3Unzip3Id xs) | (unzip3 xs)
  _ | rec | (_, _, _) = rewrite rec in Refl

export
zipWithComma : (xs : IVect n tyf0) ->
               (ys : IVect n tyf1) ->
               zipWith (,) xs ys = zip xs ys
zipWithComma [] [] = Refl
zipWithComma (x :: xs) (y :: ys) = rewrite zipWithComma xs ys in Refl

export
zipWith3Comma : (xs : IVect n tyf0) ->
                (ys : IVect n tyf1) ->
                (zs : IVect n tyf2) ->
                zipWith3 (\x, y, z => (x, y, z)) xs ys zs = zip3 xs ys zs
zipWith3Comma [] [] [] = Refl
zipWith3Comma (x :: xs) (y :: ys) (z :: zs) = rewrite zipWith3Comma xs ys zs in Refl

export
zipWithIsMap : {0 tyf0, tyf1, tyf2 : TyF n} ->
               (f : {idx : Fin n} -> (tyf0 idx, tyf1 idx) -> tyf2 idx) ->
               (xs : IVect n tyf0) ->
               (ys : IVect n tyf1) ->
               zipWith (\p, q => f (p, q)) xs ys = map f (zip xs ys)
zipWithIsMap f [] [] = Refl
zipWithIsMap f (x :: xs) (y :: ys) = rewrite zipWithIsMap (\y => f y) xs ys in Refl

export
zipWith3IsMap : {0 tyf0, tyf1, tyf2, tyf3 : TyF n} ->
                (f : {idx : Fin n} -> (tyf0 idx, tyf1 idx, tyf2 idx) -> tyf3 idx) ->
                (xs : IVect n tyf0) ->
                (ys : IVect n tyf1) ->
                (zs : IVect n tyf2) ->
                zipWith3 (\p, q, r => f (p, q, r)) xs ys zs = map f (zip3 xs ys zs)
zipWith3IsMap f [] [] [] = Refl
zipWith3IsMap f (x :: xs) (y :: ys) (z :: zs) = rewrite zipWith3IsMap (\y => f y) xs ys zs in Refl

infixl 8 -?
(-?) : (n : _) -> (x : Fin (S n)) -> Fin (S n `minus` finToNat x)
n -? FZ = last' n
S n -? FS x = n -? x

infixl 8 ?+?
(?+?) : {m, n : _} -> Fin m -> Fin (S n) -> Fin (m + n)
(?+?) {m = S m} FZ y = weakenLTE y (LTESucc (rewrite plusCommutative m n in lteAddRight _))
(?+?) {m = S _} (FS x) y = FS (x ?+? y)

lteLemma : (n', n : _) ->
           (len : Fin (S n)) ->
           finToNat len = S n' ->
           n' `LTE` n
lteLemma 0 _ _ _ = LTEZero
lteLemma (S _) 0 FZ Refl impossible
lteLemma (S _) 0 (FS x) _ = absurd x
lteLemma (S _) (S n) FZ Refl impossible
lteLemma (S n') (S n) (FS x) prf = LTESucc $ lteLemma n' n x (injective prf)

infix 8 +!
(+!) : {n : _} ->
       (len : Fin (S n)) ->
       (idx : Fin (finToNat len)) ->
       Fin n
(+!) len idx with (finToNat len) proof p
 _ | Z = absurd idx
 _ | S n' = let lte = lteLemma n' n len p
             in coerce (rewrite p in plusMinusLte _ _ lte) $ (n -? len) ?+? idx

voldrConsAcc : (0 tyf : TyF n) ->
               TyF (S n)
voldrConsAcc tyf len = IVect (finToNat len) (\idx => tyf (len +! idx))

voldrConsFun : (0 tyf : TyF n) ->
               (idx : Fin n) ->
               (len : Fin n) ->
               idx = complement len ->
               tyf idx ->
               voldrConsAcc tyf (weaken len) ->
               voldrConsAcc tyf (FS len)
voldrConsFun tyf idx len prf x acc = let res = x :: acc in ?rhs

export
voldrConsId : {n : _} ->
              {0 tyf : TyF n} ->
              (xs : IVect n tyf) ->
              voldr {accTy = voldrConsAcc tyf} (voldrConsFun tyf) [] xs
              ~=~
              xs
