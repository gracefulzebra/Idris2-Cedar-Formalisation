module CedarLite.Evaluation

import CedarLite.EntityStore
import CedarLite.Syntax
import CedarLite.Types

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

convertVal : SubType x y -> Value x -> Value y
convertVal Refl val = val 
convertVal TB VTRUE = VB True
convertVal FB VFALSE = VB False
convertVal (Trans a b) val = convertVal b (convertVal a val)

public export
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
