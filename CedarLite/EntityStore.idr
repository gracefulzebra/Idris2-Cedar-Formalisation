module CedarLite.EntityStore

import CedarLite.Syntax
import CedarLite.Types

|||Entity Store Spec
public export
data EntityStore : Type 
  where
    ES : List (String, String, String) 
      -> EntityStore

|||Helper Function for Finding <Maybe> Entity in Store
public export
entityLookup : EntityStore -> String -> String -> Maybe String
entityLookup (ES[]) eType eId = Nothing -- Empty Store / No Store Left to Search
entityLookup (ES((eTypei, eIdi, eDatai) :: xs)) eType eId =
  if (eType == eTypei) && (eId == eIdi) then 
    Just eDatai -- Article Found in Entity Store
  else
    entityLookup (ES xs) eType eId --Recurse Over Remainder of Entity Store

||| The authorisation context but with a specification.
public export
data AuthContext : AuthContextSpec -> Type where
  AC : Value (E p_id)
    -> Value (E a_id)
    -> Value (E r_id)
    -> Value (R ctxt)
    -> EntityStore
    -> AuthContext (ACS p_id a_id r_id ctxt)