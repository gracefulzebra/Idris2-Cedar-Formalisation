module Formalisation.Terms

--Deps =====================
import public Data.List.Elem

%default total
--Deps =====================

public export
data Ty = BOOL | STRING

public export
data Term : (  context : List Ty)
           -> (0 type    : Ty)
                      -> Type
    where
      B : Bool -> Term ctxt BOOL
      --S : String -> Term ctxt STRING

      And : (l,r : Term ctxt BOOL)
                -> Term ctxt BOOL

      Or  : (l,r : Term ctxt BOOL)
                -> Term ctxt BOOL

      Var : (idx : Elem type ctxt)
                -> Term ctxt type

      Let : {typeT, typeB : Ty}
         -> (this : Term ctxt typeT)
         -> (body : Term (typeT :: ctxt) typeB)
                 -> Term ctxt typeB
    