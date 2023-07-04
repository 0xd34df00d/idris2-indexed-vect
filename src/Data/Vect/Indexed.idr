module Data.Vect.Indexed

import public Data.Fin

%default total

public export
TyF : Nat -> Type
TyF n = Fin n -> Type

public export
data IVect : (n : Nat) -> (0 tyf : TyF n) -> Type where
  Nil  : IVect Z tyf
  (::) : {0 tyf : Fin (S n) -> Type} ->
         (x : tyf FZ) ->
         (xs : IVect n (\idx => tyf (FS idx))) ->
         IVect (S n) tyf

%name IVect xs, ys

public export
tabulate : {n : Nat} ->
           {0 tyf : _} ->
           (f : (idx : Fin n) -> tyf idx) ->
           IVect n tyf
tabulate {n = Z} _ = Nil
tabulate {n = S n} f = f FZ :: tabulate (\idx => f (FS idx))

infix 7 ~>
public export
(~>) : {n : Nat} -> (tyf, tyf' : TyF n) -> Type
tyf ~> tyf' = {idx : Fin n} -> tyf idx -> tyf' idx

public export
map : {0 tyf' : _} ->
      (f : tyf ~> tyf') ->
      IVect n tyf ->
      IVect n tyf'
map f [] = []
map f (x :: xs) = f x :: map (\y => f y) xs
