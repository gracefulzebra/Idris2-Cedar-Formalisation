module Formalisation.Terms

--Deps =====================
import public Data.List.Elem
--import public Formalisation.Custom

%default total
--Deps =====================

public export
data Ty = BOOL | STRING | EntityRef

public export
data Term : (  context : List Ty)
           -> (0 type    : Ty)
                      -> Type
    where
      B : Bool -> Term ctxt BOOL
      S : String -> Term ctxt STRING

      ERef : (id : String) 
                -> Term ctxt STRING 
                -> Term ctxt EntityRef

      And : (l,r : Term ctxt BOOL)
                -> Term ctxt BOOL
      
      --Distinct equality term for each Type.
      EqString  : (l,r : Term ctxt STRING)
                -> Term ctxt BOOL
            
      EqBool  : (l,r : Term ctxt BOOL)
                -> Term ctxt BOOL

      EqERef  : (l,r : Term ctxt EntityRef)
                -> Term ctxt BOOL

      Or  : (l,r : Term ctxt BOOL)
                -> Term ctxt BOOL

      Var : (idx : Elem type ctxt)
                -> Term ctxt type

      Let : {typeT, typeB : Ty}
         -> (this : Term ctxt typeT)
         -> (body : Term (typeT :: ctxt) typeB)
                 -> Term ctxt typeB
    