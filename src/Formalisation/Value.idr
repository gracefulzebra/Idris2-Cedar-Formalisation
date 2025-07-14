module Formalisation.Value

--Deps =====================
import Formalisation.Terms
--Deps =====================

public export
data Value : (term : Term ctxt type)
                  -> Type
      where
        --S : Value (S s)
        B : Value (B b)