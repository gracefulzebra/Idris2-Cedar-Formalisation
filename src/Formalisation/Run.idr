module Formalisation.Run

import Formalisation.Terms
import Formalisation.Progress
import Formalisation.Evaluation
  
export covering
run : {0 type : Ty}
    -> (this : Term Nil type)
            -> Maybe (that : Term Nil type ** Reduces this that)
run this with (evaluate forever this)
  run this | (Eval steps (IsValue {term} x))
    = Just (term ** steps)
  run this | (Eval steps NoFuel)
    = Nothing
