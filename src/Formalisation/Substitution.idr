module Formalisation.Substitution

--Deps =====================
import Formalisation.Terms
import Formalisation.Renaming

%default total
--Deps =====================

public export
weakens : {old, new : List Ty}

        -> (f : {ty : Ty}
            -> Elem ty old -> Term new ty)

        -> ({ty,type' : Ty}
            -> Elem ty  (type' :: old)
            -> Term     (type' :: new) ty)

weakens f Here
    = Var Here
weakens f (There rest)
    = rename There (f rest)

public export
subst : {old, new : List Ty}
      -> (f : {ty : Ty}
            -> Elem ty old
            -> Term    new ty)
      -> ({ty : Ty}
            -> Term old ty
            -> Term new ty)

subst f (Var x)
  = f x

subst f (B x)
  = B x

subst f (S x)
  = S x

subst f (ERef tag t)
  = ERef tag (subst f t)

subst f (And l r)
  = And (subst f l) (subst f r)

subst f (EqBool l r)
  = EqBool (subst f l) (subst f r)

subst f (EqString l r)
  = EqString (subst f l) (subst f r)

subst f (EqERef l r)
  = EqERef (subst f l) (subst f r)

subst f (Or l r)
  = Or (subst f l) (subst f r)

subst f (Let this body)
  = Let (subst f this) (subst (weakens f) body)

namespace Single

  public export
  subst : {typeA,typeB : Ty}
        -> {ctxt : List Ty}
        -> (this          : Term           ctxt  typeB)
        -> (inThis        : Term (typeB :: ctxt) typeA)
                        -> Term           ctxt  typeA

  subst {ctxt} {typeA} {typeB} this inThis
      = subst (apply this) inThis

    where
      apply : {typeA,typeB : Ty}
            -> {ctxt        : List Ty}
            -> (this   : Term                 ctxt   typeB)
            -> (idx    : Elem typeA (typeB :: ctxt))
                      -> Term                 ctxt   typeA
      apply this Here
        = this

      apply this (There rest)
        = Var rest
