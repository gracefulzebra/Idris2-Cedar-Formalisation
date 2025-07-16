module Formalisation.Tests

import Formalisation.Terms
import Formalisation.Run

%default total

public export
example : Term Nil BOOL
example
      = Or (B False) (B False)

example1 : Term Nil STRING
example1 = S "TestString"