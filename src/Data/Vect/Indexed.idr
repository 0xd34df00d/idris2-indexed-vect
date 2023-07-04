module Data.Vect.Indexed

import public Data.Fin

public export
data IVect : (n : Nat) -> (tyf : Fin n -> Type) -> Type where
  Nil  : IVect Z tyf
  (::) : {tyf : Fin (S n) -> Type} ->
         (x : tyf FZ) ->
         (xs : IVect n (\idx => tyf (FS idx))) ->
         IVect (S n) tyf

%name IVect xs, ys

public export
tabulate : {n : Nat} ->
           {tyf : Fin n -> Type} ->
           (f : (idx : Fin n) -> tyf idx) ->
           IVect n tyf
tabulate {n = Z} _ = Nil
tabulate {n = S n} f = f FZ :: tabulate (\idx => f (FS idx))
