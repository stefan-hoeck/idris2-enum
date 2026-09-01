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
conIndexInjectiveName : Named a => a -> Name
conIndexInjectiveName v = funName v "conIndexInjective"

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
conIndexInjectiveClaim : Visibility -> (cifun, fun : Name) -> (p : TypeInfo) -> Decl
conIndexInjectiveClaim vis cifun fun p =
  let civ := var cifun
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
conIndexInjectiveDef : (fun : Name) -> TypeInfo -> Decl
conIndexInjectiveDef f p = def f $ map cclause p.cons
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

||| Generates a proof that the `conIndexXY` function is injective.
export
ConIndexInjectiveVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
ConIndexInjectiveVis vis nms p =
  let ci   := conIndexName p
      fun  := conIndexInjectiveName p
   in Right
        [ TL (conIndexInjectiveClaim vis ci fun p.info) (conIndexInjectiveDef fun p.info)
        ]

||| Alias for `ConIndexInjectiveVis Export`
export %inline
ConIndexInjective : List Name -> ParamTypeInfo -> Res (List TopLevel)
ConIndexInjective = ConIndexInjectiveVis Export

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
