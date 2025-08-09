module CedarLite.Syntax

import public Data.List.Quantifiers

import CedarLite.Types

mutual
  ||| A field maps a label to a term.
  public export
  data Field : (acs   : AuthContextSpec)
           ->  (fspec : (String, Ty))
                     -> Type
    where
      F : (label : String)
       -> (v     : Term acs ty)
                -> Field acs (label, ty)

  ||| Core cedar expressions
  public export
  data Term : AuthContextSpec -> Ty -> Type
    where
      S : String -> Term acs STR
      B : Bool   -> Term acs BOOL

      BTRUE : Term acs TRUE
      BFALSE : Term acs FALSE

      ERef : (id : String)
          -> (tm : Term acs STR)
                -> Term acs (E id)

      Struct : All (Field acs) kvs -> Term acs (R kvs)

      EqualString : Term acs STR -> Term acs STR -> Term acs BOOL
      EqualEntity : Term acs (E eId) -> Term acs (E eId) -> Term acs BOOL
      EqualSelf : Term acs ty -> Term acs TRUE

      And : Term acs BOOL -> Term acs BOOL -> Term acs BOOL

      Has : Term acs (R pairs) -> String -> Term acs BOOL

      Dot : Term acs (R pairs) -> String -> Term acs STR

      VarPrinciple : Term (ACS p a r cs) (E p)
      VarAction    : Term (ACS p a r cs) (E a)
      VarResource  : Term (ACS p a r cs) (E r)
      VarContext   : Term (ACS p a r cs) (R cs)

      Convert : SubType x y -> Term acs x -> Term acs y

mutual
  ||| A records field but as a value.
  public export
  data VField : (String, Ty) -> Type
    where
      VF : (label : String)
        -> (v     : Value ty)
                 -> VField (label,ty)

  ||| Terms that are values
  public export
  data Value : Ty -> Type
    where
      VB : Bool -> Value BOOL
      VTRUE : Value TRUE
      VFALSE : Value FALSE
      VS : String -> Value STR
      VERef : (id : String) -> Value STR -> Value (E id)
      VStruct : All VField kvs -> Value (R kvs)