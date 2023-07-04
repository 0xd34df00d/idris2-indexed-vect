module Data.Vect.Indexed.Properties

import Data.Vect.Indexed

%default total

export
mapFusion : {tyf0, tyf1, tyf2 : _} ->
            (f1 : tyf0 ~> tyf1) ->
            (f2 : tyf1 ~> tyf2) ->
            (vec : IVect n tyf0) ->
            map f2 (map f1 vec) = map (f2 . f1) vec
mapFusion f1 f2 [] = Refl
mapFusion f1 f2 (x :: xs) = rewrite mapFusion (\y => f1 y) (\y => f2 y) xs in Refl

export
mapId : {tyf : _} ->
        (vec : IVect n tyf) ->
        map (\x => x) vec = vec
mapId [] = Refl
mapId (x :: xs) = rewrite mapId xs in Refl
