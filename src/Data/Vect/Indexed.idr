module Data.Vect.Indexed

import public Data.Fin
import Data.Vect
import Decidable.Equality

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

%name IVect xs, ys, zs

export
{x : tyf _} -> Injective (Indexed.(::) {tyf} x) where
  injective Refl = Refl

export
{xs : _} -> Injective (\x => Indexed.(::) {tyf} x xs) where
  injective Refl = Refl

export
{tyf : _} -> Biinjective (Indexed.(::) {tyf}) where
  biinjective Refl = (Refl, Refl)

public export
tabulate : {n : Nat} ->
           {0 tyf : _} ->
           (f : (idx : Fin n) -> tyf idx) ->
           IVect n tyf
tabulate {n = Z} _ = Nil
tabulate {n = S n} f = f FZ :: tabulate (\idx => f (FS idx))

public export
index : (1 idx : Fin n) ->
        (1 vec : IVect n tyf) ->
        tyf idx
index FZ (x :: _) = x
index (FS idx) (_ :: xs) = idx `index` xs


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

export
({idx : Fin n} -> DecEq (tyf idx)) => DecEq (IVect n tyf) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = decEqCong2 (x `decEq` y) (xs `decEq` ys)

public export
toVect : ({idx : Fin n} -> tyf idx -> a) ->
         IVect n tyf ->
         Vect n a
toVect _ [] = []
toVect f (x :: xs) = f x :: toVect f xs

public export
fromVect : Vect n a ->
           IVect n (const a)
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs

namespace Zippable
  public export
  zipTyF : (tyf0, tyf1 : TyF n) ->
           TyF n
  zipTyF tyf0 tyf1 = \idx => (tyf0 idx, tyf1 idx)

  public export
  zip3TyF : (tyf0, tyf1, tyf2 : TyF n) ->
            TyF n
  zip3TyF tyf0 tyf1 tyf2 = \idx => (tyf0 idx, tyf1 idx, tyf2 idx)

  public export
  zip : IVect n tyf0 ->
        IVect n tyf1 ->
        IVect n (zipTyF tyf0 tyf1)
  [] `zip` [] = []
  (x :: xs) `zip` (y :: ys) = (x, y) :: (xs `zip` ys)

  public export
  zip3 : IVect n tyf0 ->
         IVect n tyf1 ->
         IVect n tyf2 ->
         IVect n (zip3TyF tyf0 tyf1 tyf2)
  zip3 [] [] [] = []
  zip3 (x :: xs) (y :: ys) (z :: zs) = (x, y, z) :: zip3 xs ys zs

  public export
  unzip : IVect n (zipTyF tyf0 tyf1) ->
          (IVect n tyf0, IVect n tyf1)
  unzip [] = ([], [])
  unzip ((x0, x1) :: xs) = let (xs0, xs1) = unzip xs
                            in (x0 :: xs0, x1 :: xs1)
