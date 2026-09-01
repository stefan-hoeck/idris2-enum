module Main

import Derive.Enum
import Large

%default total
%language ElabReflection

data MyEnum : Type where
  M1 : MyEnum
  M2 : MyEnum
  M3 : MyEnum
  M4 : MyEnum
  M5 : MyEnum
  M6 : MyEnum
  M7 : MyEnum
  M8 : MyEnum

%runElab derive "MyEnum" [Show,Eq,Ord,Finite,ToIndex,ToIndexInjective,ValuesComplete]

toIndex : MyEnum -> Index 8
toIndex x = I (cast $ conIndexMyEnum x) @{conIndexLtMyEnum x}

-- This is just a dummy. What we actually want is that this file
-- typechecks when "running" the test.
main : IO ()
main = putStrLn "All is well"
