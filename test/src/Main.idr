module Main

import DependentTypeTest as DependentType
import DependentPairTypeTest as DependentPairType

main : IO ()
main = do
  DependentType.spec
  DependentPairType.spec
