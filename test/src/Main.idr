module Main

import DependentTypeTest as DependentType

main : IO ()
main = do
  DependentType.spec
