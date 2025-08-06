module CedarLite

-- TO gain access to the `All` quantifier
import public Data.List.Quantifiers

||| Some Cedar Types
public export
data Ty = BOOL
        | STR
        | E String               -- Entities
        | R (List (String, Ty))  -- Records

||| The Specfication of an Authorisation Request.
public export
data AuthContextSpec
  = ACS String               -- principle
        String               -- action
        String               -- resource
        (List (String, Ty))  -- context

|||Entity Store Spec
public export
data EntityStore : Type 
  where
    ES : List (String, String, String) 
      -> EntityStore

|||Helper Function for Finding <Maybe> Entity in Store
entityLookup : EntityStore -> String -> String -> Maybe String
entityLookup (ES[]) eType eId = Nothing -- Empty Store / No Store Left to Search
entityLookup (ES((eTypei, eIdi, eDatai) :: xs)) eType eId =
  if (eType == eTypei) && (eId == eIdi) then 
    Just eDatai -- Article Found in Entity Store
  else
    entityLookup (ES xs) eType eId --Recurse Over Remainder of Entity Store 

mutual
  ||| A field maps a label to a term.
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
      B : Bool   -> Term acs BOOL
      S : String -> Term acs STR

      ERef : (id : String)
          -> (tm : Term acs STR)
                -> Term acs (E id)

      Struct : All (Field acs) kvs -> Term acs (R kvs)

      EqualString : Term acs STR -> Term acs STR -> Term acs BOOL
      EqualEntity : Term acs (E eId) -> Term acs (E eId) -> Term acs BOOL

      And : Term acs BOOL -> Term acs BOOL -> Term acs BOOL

      Has : Term acs (R pairs) -> String -> Term acs BOOL

      Dot : Term acs (R pairs) -> String -> Term acs STR

      VarPrinciple : Term (ACS p a r cs) (E p)
      VarAction    : Term (ACS p a r cs) (E a)
      VarResorce   : Term (ACS p a r cs) (E r)
      VarContext   : Term (ACS p a r cs) (R cs)

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
      VS : String -> Value STR
      VERef : (id : String) -> Value STR -> Value (E id)
      VStruct : All VField kvs -> Value (R kvs)

||| The authorisation context but with a specification.
public export
data AuthContext : AuthContextSpec -> Type where
  AC : Value (E p_id)
    -> Value (E a_id)
    -> Value (E r_id)
    -> Value (R ctxt)
    -> EntityStore
    -> AuthContext (ACS p_id a_id r_id ctxt)

||| Helper Function for Checking Field From Context
hasField : String -> All VField pairs -> Bool
hasField fieldName [] = False
hasField fieldName (VF label _ :: xs) = 
  if fieldName == label
    then True  
    else hasField fieldName xs

||| Helper Function for Getting Field From Context
getField : String -> All VField pairs -> Maybe (Value STR)
getField fieldName [] = Nothing
getField fieldName (VF label val :: xs) =
  if fieldName == label then
    case val of
      VS str => Just (VS str)
      _      => Nothing 
  else getField fieldName xs 


||| Policy Definitions
public export
data Effect = PERMIT | FORBID

Eq Effect where
  PERMIT == PERMIT = True
  FORBID == FORBID = True
  _ == _ = False

public export
data Decision = ALLOW | DENY

public export
data Policy : AuthContextSpec -> Type where
  MkPolicy : Effect -> Term acs BOOL -> Policy acs

mutual
  public export
  eval : AuthContext acs -> Term acs ty -> Value ty
  eval ac (B x) = VB x
  eval ac (S str) = VS str
  
  eval ac (ERef id tm) = 
    case eval ac tm of
      VS eId => 
        case ac of
          AC _ _ _ _ store => 
            case entityLookup store id eId of
              Just eData => VERef id (VS eData)  
              Nothing => VERef id (VS eId) --Placeholder for unresolvable VERef
      _ => VERef id (VS "Invalid")

  eval ac (EqualString a b) =
    case (eval ac a, eval ac b) of
      (VS aStr, VS bStr) => VB (aStr == bStr) --Matching VS Values = Boolean Comparison
      _                  => VB False -- Mismatching or non VS Values = Rejection

  eval ac (EqualEntity a b) =
    case (eval ac a, eval ac b) of
      (VERef _ (VS aData), VERef _ (VS bData)) => VB (aData == bData) --Only Matching on Dereferenced ERefs
      _                                        => VB False -- Mismatching or non ERef Values = Rejection

  eval ac (And a b) =
    case (eval ac a, eval ac b) of
      (VB True, VB True) => VB True -- Matching True VB Values
      _                  => VB False -- Mismatching or non VB Values = Rejection

  eval ac (Has rec fieldName) =
    case eval ac rec of
      VStruct fields => VB (hasField fieldName fields)
      _               => VB False

  eval ac (Dot rec fieldName) =
    case eval ac rec of
      VStruct fields => case getField fieldName fields of
                          Just val => val
                          Nothing => VS "FIELD NOT FOUND"
      _              => VS "NOT A RECORD"

  eval ac (Struct x) = VStruct (evalStruct ac x)

  eval (AC x y z w store) VarPrinciple = x
  eval (AC x y z w store) VarAction = y
  eval (AC x y z w store) VarResorce = z
  eval (AC x y z w store) VarContext = w

  ||| Dealing with fields
  evalStruct : AuthContext acs
            -> All (Field acs) kvs
            -> All VField      kvs
  evalStruct x [] = []
  evalStruct x (F l y :: z) with (eval x y)
    evalStruct x (F l y :: z) | with_pat with (evalStruct x z)
      evalStruct x (F l y :: z) | h | t = VF l h :: t


cedarEval : AuthContext acs -> Term acs BOOL -> Value BOOL
cedarEval = eval

public export
evalPolicy : AuthContext acs -> Policy acs -> (Effect, Bool)
evalPolicy ac (MkPolicy effect condition) =
  case eval ac condition of
    VB result => (effect, result)
    _         => (effect, False)

public export    
auth : AuthContext acs -> List (Policy acs) -> Decision
auth ac policies =
  let results = map (evalPolicy ac) policies
      permits = filter (\(eff, cond) => eff == PERMIT && cond) results
      forbids = filter (\(eff, cond) => eff == FORBID && cond) results
  in case (length permits > 0, length forbids > 0) of
      (True, False) => ALLOW --Explicit Permit
      _             => DENY --Default Deny 


-- [ EOF ]