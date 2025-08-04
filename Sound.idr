module Sound

import CedarLite

|||Predicate on Defined Types
data IsType : Value ty -> Ty -> Type where
    BoolValid : IsType (VB b) BOOL
    StringValid : IsType (VS s) STR
    EntityValid : (id : String) -> IsType (VERef id tm) (E id)
    --RecordValid : (pairs : String, Ty) -> IsType (VField) FIX



