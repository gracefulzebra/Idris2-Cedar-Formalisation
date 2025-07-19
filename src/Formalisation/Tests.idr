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

example2 : Term Nil BOOL
example2 = EqString (S "Peter") (S "Peter")

example3 : Term Nil BOOL 
example3 = EqBool (B True) (B True)