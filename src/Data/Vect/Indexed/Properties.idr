module Data.Vect.Indexed.Properties

import Data.Vect
import Data.Vect.Indexed

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
zipUnzipId ((x0, x1) :: xs) with (zipUnzipId xs) | (unzip xs)
  _ | rec | (xs0, xs1) = rewrite rec in Refl
