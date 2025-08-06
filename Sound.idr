module Sound

import CedarLite

|||Predicate on Defined Types
data IsType : Value ty -> Ty -> Type where
    BoolValid : IsType (VB b) BOOL
    StringValid : IsType (VS s) STR
    EntityValid : (id : String) -> IsType (VERef id tm) (E id)
    RecordValid : (pairs : List (String, Ty)) -> IsType (VStruct fields) (R pairs)

wellTyped : (ac :AuthContext acs) -> (t: Term acs ty) -> IsType (eval ac t) ty

wellTyped ac (B b) = BoolValid
wellTyped ac (S s) = StringValid
wellTyped ac (ERef id tm) = ?eref_rhs

wellTyped ac (EqualString a b) = BoolValid
wellTyped ac (EqualEntity a b) = BoolValid
wellTyped ac (And a b) = BoolValid
wellTyped ac (Has rec field) = BoolValid

wellTyped ac (Dot rec field) = StringValid



-- Context variables (need work - these extract from AuthContext)
wellTyped ac VarPrinciple = ?varprinc_rhs
wellTyped ac VarAction = ?varAct_rhs
wellTyped ac VarResorce = ?varRes_rhs
wellTyped ac VarContext = ?varCtxt_rhs

-- Struct case (needs coordination with evalStruct)
wellTyped ac (Struct fields) = ?struc_rhs

-- [ EOF ]