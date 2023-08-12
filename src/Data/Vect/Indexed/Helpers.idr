module Data.Vect.Indexed.Helpers

import Data.Vect
import Data.Fin
import Data.Fin.Extra

public export
last' : (n : _) -> Fin (S n)
last' Z = FZ
last' (S n) = FS (last' n)

public export
complementLast : (n : _) ->
                 complement (last' n) = FZ
complementLast Z = Refl
complementLast (S n) = rewrite complementLast n in Refl

public export
complementWeaken : (x : Fin n) ->
                   FS (complement x) = complement (weaken x)
complementWeaken FZ = Refl
complementWeaken (FS x) = rewrite sym $ complementWeaken x in Refl

public export
complementWeaken' : {x, y : _} ->
                    x = complement y ->
                    FS x = complement (weaken y)
complementWeaken' Refl = complementWeaken y

public export
finToNatLast : (n : _) ->
               finToNat (last' n) = n
finToNatLast Z = Refl
finToNatLast (S n) = cong S (finToNatLast n)
