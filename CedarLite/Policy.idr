module CedarLite.Policy

import CedarLite.EntityStore
import CedarLite.Evaluation
import CedarLite.Syntax
import CedarLite.Types

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