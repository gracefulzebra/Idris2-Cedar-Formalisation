module Formalisation.Custom

%default total

public export
data EntityType = User | Role | Photo | Action

public export
record EntityUID where
  constructor MkEntity
  entityType : EntityType
  name       : String