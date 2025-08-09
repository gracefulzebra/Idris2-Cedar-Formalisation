module CedarLite.Types

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