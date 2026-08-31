module Data.Enum

import Derive.Prelude
import public Data.Finite
import public Data.List.Elem
import public Data.Prim.Bits32
import public Decidable.HDecEq

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Primitive Indices
--------------------------------------------------------------------------------

public export
record Index (n : Bits32) where
  constructor I
  val : Bits32
  {auto 0 prf : val < n}

%runElab deriveIndexed "Index" [Show,Eq,Ord]

export
tryIndex : {r : _} -> Bits32 -> Maybe (Index r)
tryIndex n =
  case lt n r of
    Nothing0 => Nothing
    Just0 v  => Just (I n)

public export
fromInteger : (n : Integer) -> (0 p : cast n < r) => Index r
fromInteger n = I (cast n)

public export
Zero : (0 prf : 0 < n) => Index n
Zero = I 0

export
0 ltProof : (v : Bits32) -> (0 prf : v < n) => lt (cast v) (cast n) === True
ltProof v = believe_me $ Builtin.Refl {x = True}

export %inline
toFin : Index n -> Fin (cast n)
toFin (I v) = bits32ToFin v n

export %inline
Cast (Index n) Integer where
  cast (I v) = cast v

export %inline
Cast (Index n) Bits32 where
  cast (I v) = v

--------------------------------------------------------------------------------
-- Enum Interface
--------------------------------------------------------------------------------

||| Verified enumerations.
|||
||| Provides a function for converting a value of the given type to an
||| `Index n` of the given size.
|||
||| In addition, proves that `Finite.value` holds every value there is and
||| that `toIndex` is injective.
|||
||| With these proofs we can use a value of type `t` as an index into a
||| (potentially dependent) array.
public export
interface Finite t => Enum (0 t : Type) (0 n : Bits32) | t where
  constructor MkEnum
  toIndex : t -> Index n

  0 toIndexInjective : (x,y : t) -> toIndex x === toIndex y -> x === y

  0 valuesComplete : (x : t) -> Elem x Finite.values

export %inline
enumToFin : Enum t n => t -> Fin (cast n)
enumToFin = toFin . toIndex

export %inline
enumToBits32 : Enum t n => t -> Bits32
enumToBits32 = cast . toIndex

export %inline
enumToInteger : Enum t n => t -> Integer
enumToInteger = cast . toIndex

export
Enum Bool 2 where
  toIndex False = 0
  toIndex True  = 1

  toIndexInjective False False Refl = Refl
  toIndexInjective True True Refl = Refl

  valuesComplete False = Here
  valuesComplete True = There Here

export
Enum Ordering 3 where
  toIndex LT = 0
  toIndex EQ = 1
  toIndex GT = 2

  toIndexInjective LT LT Refl = Refl
  toIndexInjective EQ EQ Refl = Refl
  toIndexInjective GT GT Refl = Refl

  valuesComplete LT = Here
  valuesComplete EQ = There Here
  valuesComplete GT = There $ There Here

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

public export
inList : HDecEq i => (v : i) -> List i -> Bool
inList v []        = False
inList v (x :: xs) =
  case hdecEq v x of
    Nothing0 => inList v xs
    Just0 _  => True

export
0 inListImpliesElem : HDecEq i => (v : i) -> inList v is === True -> Elem v is
inListImpliesElem v prf {is = []}    = absurd prf
inListImpliesElem v prf {is = x::xs} with (hdecEq v x)
  _ | Nothing0  = There $ inListImpliesElem v prf {is = xs}
  _ | Just0 p   = rewrite p in Here
