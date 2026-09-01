module Derive.Enum

import public Data.Enum
import public Derive.Finite
import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

export
conIndexLtName : Named a => a -> Name
conIndexLtName v = funName v "conIndexLt"

export
toIndexName : Named a => a -> Name
toIndexName v = funName v "toIndex"

export
toIndexInjectiveName : Named a => a -> Name
toIndexInjectiveName v = funName v "toIndexInjective"

export
valuesCompleteName : Named a => a -> Name
valuesCompleteName v = funName v "valuesComplete"

||| Top-level function declaration of a proof that all constructor indexes
||| are less than the total number of constructors.
export
conIndexLtClaim : Visibility -> (cifun, fun : Name) -> (p : TypeInfo) -> Decl
conIndexLtClaim vis cifun fun p =
  let civ := var cifun
      tot := primVal (B32 $ cast $ length p.cons)
      arg := MkArg MW ExplicitArg (Just "v") p.applied
      tpe := piAll `(cast {to = Bits32} (~(civ) v) < ~(tot)) (p.implicits ++ [arg])
   in claim M0 vis [] fun tpe

||| Top-level function declaration of a proof that all the `conIndexXY`
||| function is injective.
export
toIndexInjectiveClaim : Visibility -> (tifun, fun : Name) -> (p : TypeInfo) -> Decl
toIndexInjectiveClaim vis tifun fun p =
  let civ := var tifun
      a1  := MkArg MW ExplicitArg (Just "x") p.applied
      a2  := MkArg MW ExplicitArg (Just "y") p.applied
      prf := MkArg MW ExplicitArg (Just "prf") `(~(civ) x === ~(civ) y)
      tpe := piAll `(x === y) (p.implicits ++ [a1,a2,prf])
   in claim M0 vis [] fun tpe

||| Top-level function declaration of a proof that every value is
||| indeed included in `Data.Finite.values`.
export
valuesCompleteClaim : Visibility -> (fun : Name) -> (p : TypeInfo) -> Decl
valuesCompleteClaim vis fun p =
  let arg := MkArg MW ExplicitArg (Just "v") p.applied
      tpe := piAll `(Data.List.Elem.Elem v Data.Finite.values) (p.implicits ++ [arg])
   in claim M0 vis [] fun tpe

||| Top-level function declaration for a conversion of a data constructor
||| to a value of type `Index n`, where `n` is the number of data constructors
||| of the type.
export
toIndexClaim : Visibility -> (fun : Name) -> (p : TypeInfo) -> Decl
toIndexClaim vis fun p =
  let tot := primVal (B32 $ cast $ length p.cons)
      arg := MkArg MW ExplicitArg (Just "v") p.applied
      tpe := piAll `(Index ~(tot)) (p.implicits ++ [arg])
   in simpleClaim vis fun tpe

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
conIndexLtDef : (fun : Name) -> TypeInfo -> Decl
conIndexLtDef f p = def f $ map cclause p.cons
  where
    cclause : Con p.arty p.args -> Clause
    cclause c = patClause (var f `app` bindAny c) `(Data.Prim.Bits32.mkLT Refl)

export
toIndexDef : (fun, cif, ltp : Name) -> Decl
toIndexDef f cif ltp =
 let rhs := `(I (cast {to = Bits32} (~(var cif) v)) @{~(var ltp) v})
  in def f [patClause (var f `app` var "v") rhs]

export
toIndexInjectiveDef : (fun : Name) -> TypeInfo -> Decl
toIndexInjectiveDef f p = def f $ map cclause p.cons
  where
    cclause : Con p.arty p.args -> Clause
    cclause c = patClause (appAll f [bindAny c, bindAny c, `(Refl)]) `(Refl)

export
valuesCompleteDef : (fun : Name) -> TypeInfo -> Decl
valuesCompleteDef f p = def f (clauses [<] `(Here) p.cons)
  where
    clauses : SnocList Clause -> TTImp -> List (Con p.arty p.args) -> List Clause
    clauses sc prf []        = sc <>> []
    clauses sc prf (x :: xs) =
     let c := patClause (var f `app` bindAny x) prf
      in clauses (sc:<c) `(There ~(prf)) xs

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generates a proof that the constructor index returned by `conIndexXY` is
||| strictly less than the number of constructors.
export
ConIndexLtVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
ConIndexLtVis vis nms p =
  let ci   := conIndexName p
      fun  := conIndexLtName p
   in Right
        [ TL (conIndexLtClaim vis ci fun p.info) (conIndexLtDef fun p.info)
        ]

||| Alias for `ConIndexLtVis Export`
export %inline
ConIndexLt : List Name -> ParamTypeInfo -> Res (List TopLevel)
ConIndexLt = ConIndexLtVis Export

||| Generates a conversion of data constructors to values of type `Index n`,
||| where `n` is the number of data constructors of the given type.
|||
||| This includes `ConIndexLtVis`
export
ToIndexVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
ToIndexVis vis nms p =
  let fun  := toIndexName p
      cif  := conIndexName p
      ltp  := conIndexLtName p
   in sequenceJoin
        [ ConIndexLtVis vis nms p
        , Right [TL (toIndexClaim vis fun p.info) (toIndexDef fun cif ltp)]
        ]

||| Alias for `ToIndexVis Export`
export %inline
ToIndex : List Name -> ParamTypeInfo -> Res (List TopLevel)
ToIndex = ToIndexVis Export

||| Generates a proof that the `toIndexXY` function is injective.
export
ToIndexInjectiveVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
ToIndexInjectiveVis vis nms p =
  let ti   := toIndexName p
      fun  := toIndexInjectiveName p
   in Right
        [ TL (toIndexInjectiveClaim vis ti fun p.info) (toIndexInjectiveDef fun p.info)
        ]

||| Alias for `ToIndexInjectiveVis Export`
export %inline
ToIndexInjective : List Name -> ParamTypeInfo -> Res (List TopLevel)
ToIndexInjective = ToIndexInjectiveVis Export

||| Generates a proof that the `Data.Finite.values` indeed contains every
||| possible value. This currently only works for enum types.
export
ValuesCompleteVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
ValuesCompleteVis vis nms p =
  let fun := valuesCompleteName p
   in Right
        [ TL (valuesCompleteClaim vis fun p.info) (valuesCompleteDef fun p.info)
        ]

||| Alias for `ValuesCompleteVis Export`
export %inline
ValuesComplete : List Name -> ParamTypeInfo -> Res (List TopLevel)
ValuesComplete = ValuesCompleteVis Export
