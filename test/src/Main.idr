module Main

import Derive.Enum
import Large
import IndexImpl

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

%runElab derive "MyEnum" [Show,Enum]

toIndex : MyEnum -> Index 8
toIndex x = I (cast $ conIndexMyEnum x) @{conIndexLtMyEnum x}

data MyTEnum : Type -> Type where
  MT1 : MyTEnum Bool
  MT2 : MyTEnum String
  MT3 : MyTEnum (Maybe Nat)
  MT4 : MyTEnum ()

%runElab deriveIndexed "MyTEnum" [TEnum]

data NatEnum : Bool -> Type where
  NE1 : NatEnum True
  NE2 : NatEnum False
  NE3 : NatEnum True
  NE4 : NatEnum False

%runElab deriveIndexed "NatEnum" [TEnum]

main : IO ()
main = Prelude.do
  traverse_ IndexImpl.check [0..500]
  putStrLn "All is well"
