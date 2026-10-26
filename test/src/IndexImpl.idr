module IndexImpl

import Data.Enum
import Data.List
import System

%default total

elemToBits32 : Elem x xs -> Bits32
elemToBits32 Here      = 0
elemToBits32 (There x) = 1 + elemToBits32 x

checkVals : (n : Bits32) -> Maybe (Index n)
checkVals n = find invalid (values {a = Index n})
  where
    invalid : Index n -> Bool
    invalid x = elemToBits32 (vcomplete x) /= x.val

export
check : (n : Bits32) -> IO ()
check n =
  case checkVals n of
    Nothing => pure ()
    Just x  => die "Error in `Index \{show n}`: value \{show x} not in `values`."
