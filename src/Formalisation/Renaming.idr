module Formalisation.Renaming

--Deps =====================
import Formalisation.Terms

%default total  
--Deps =====================

public export
weaken : (f : Elem type           old  -> Elem type           new )
      -> (    Elem type (type' :: old) -> Elem type (type' :: new))

weaken f Here
  = Here
weaken f (There rest)
  = There (f rest)

public export
rename : (f : forall ty . Elem ty old -> Elem ty new)
      -> (    forall ty . Term old ty -> Term new ty)

rename f (Var x)
  = Var (f x)

rename f (B x)
  = B x

rename f (S x)
  = S x

rename f (ERef tag t)
  = ERef tag (rename f t)

rename f (And l r)
  = And (rename f l) (rename f r)

rename f (EqBool l r)
  = EqBool (rename f l) (rename f r)

rename f (EqString l r)
  = EqString (rename f l) (rename f r)

rename f (EqERef l r)
  = EqERef (rename f l) (rename f r)

rename f (Or l r)
  = Or (rename f l) (rename f r)

rename f (Let this body)
  = Let (rename f this) (rename (weaken f) body)