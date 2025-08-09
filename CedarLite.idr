module CedarLite

-- TO gain access to the `All` quantifier
import public Data.List.Quantifiers

||| Some Cedar Types
public export
data Ty = BOOL
        | TRUE
        | FALSE
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

||| Subtyping Relations Between Singleton Types and Bool Type
public export
data SubType : (x, y : Ty) -> Type where
  Refl : SubType x x
  
  Trans : SubType x y
       -> SubType y z
       -> SubType x z
  
  TB : SubType TRUE BOOL
  FB : SubType FALSE BOOL

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
  MkPolicy : Effect 
           -> Term (ACS p a r ctxt) BOOL    -- Principal constraint
           -> Term (ACS p a r ctxt) BOOL    -- Action constraint  
           -> Term (ACS p a r ctxt) BOOL    -- Resource constraint
           -> List (Term (ACS p a r ctxt) BOOL)  -- When conditions
           -> Policy (ACS p a r ctxt)

convertVal : SubType x y -> Value x -> Value y
convertVal Refl val = val 
convertVal TB VTRUE = VB True
convertVal FB VFALSE = VB False
convertVal (Trans a b) val = convertVal b (convertVal a val)

boolValue : {ty : Ty} -> Value ty -> Bool
boolValue {ty = BOOL} (VB b) = b
boolValue {ty = TRUE} VTRUE = True
boolValue {ty = FALSE} VFALSE = False
boolValue _ = False

mutual
  public export
  eval : AuthContext acs -> Term acs ty -> Value ty
  eval ac (S str) = VS str
  eval ac (B x) = VB x

  eval ac BTRUE = VTRUE
  eval ac BFALSE = VFALSE
  
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

  eval ac (EqualSelf a) = VTRUE

  eval ac (And a b) =
    let aVal = eval ac a
        bVal = eval ac b
    in VB (boolValue aVal && boolValue bVal)

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

  eval ac (Convert prf term) = convertVal prf (eval ac term)

  eval (AC x y z w store) VarPrinciple = x
  eval (AC x y z w store) VarAction = y
  eval (AC x y z w store) VarResource = z
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
toExpr : Policy (ACS p a r ctxt) -> Term (ACS p a r ctxt) BOOL
toExpr (MkPolicy effect principalExpr actionExpr resourceExpr context) =
  let -- Combine 'when' cond
      whenExpr = case context of
        [] => B True
        [cond] => cond
        (cond :: rest) => foldl And cond rest
      scopeExpr = And (And principalExpr actionExpr) resourceExpr-- Conjunct.
  in And scopeExpr whenExpr

public export
evalPolicy : AuthContext acs -> Policy acs -> (Effect, Bool)
evalPolicy ac policy =
  let (MkPolicy effect _ _ _ _) = policy
      result = boolValue (eval ac (toExpr policy))
  in (effect, result)

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