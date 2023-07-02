module Data.Vect.Indexed

import public Data.Fin

public export
data IVect : (n : Nat) -> (tyf : Fin n -> Type) -> Type where
  Nil  : IVect Z tyf
  (::) : {tyf : Fin (S n) -> Type} ->
         (val : tyf FZ) ->
         IVect n (\idx => tyf (FS idx)) ->
         IVect (S n) tyf
