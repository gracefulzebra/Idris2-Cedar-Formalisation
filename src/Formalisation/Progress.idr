module Formalisation.Progress

--Deps =====================
import Formalisation.Terms 
import Formalisation.Value
import Formalisation.Substitution

%default total
--Deps =====================

public export
data Reduce : (this : Term ctxt type)
           -> (that : Term ctxt type)
                   -> Type
  where
    SimplifyEqL  : Reduce      this that
                -> Reduce (Eq  this      right)
                          (Eq       that right)

    SimplifyEqR  : Value       left
                -> Reduce          this that
                -> Reduce (Eq left this      )
                          (Eq left      that )

    ReduceEqBool : Reduce (Eq (B a) (B b))
                          (B  ( a  ==  b ))

    ReduceEqString : Reduce (Eq (S a) (S b))
                            (S  ( a  == b ))

    SimplifyAndL : Reduce      this that
                -> Reduce (And this      right)
                          (And      that right)

    SimplifyAndR : Value       left
                -> Reduce           this that
                -> Reduce (And left this     )
                          (And left      that)

    ReduceAnd : Reduce (And (B a)    (B b))
                        (B   (  a  &&    b))

    SimplifyOrL : Reduce      this that
               -> Reduce  (Or this      right)
                          (Or      that right)

    SimplifyOrR : Value        left
               -> Reduce            this that
               -> Reduce  (Or left this     )
                          (Or left      that)

    ReduceOr : Reduce (Or (B a)   (B b))
                        (B (a || b))

    SimplifyLet : Reduce      this that
                -> Reduce (Let this      body)
                          (Let      that body)

    ReduceLet : Value                this
              -> Reduce (Let          this body)
                        (Single.subst this body)

public export
data Progress : (term : Term Nil type)
                      -> Type
  where
    Stop : (value : Value    term)
                  -> Progress term

    Step : {that : Term Nil type}
        -> (step : Reduce   this that)
                -> Progress this

export
progress : (term : Term Nil type)
                -> Progress term

progress (Var _) impossible

progress (B x) = Stop B
progress (S x) = Stop S

progress (And l r) with (progress l)
  progress (And (B n) r) | (Stop B) with (progress r)
    progress (And (B n) (B m)) | (Stop B) | (Stop B)
      = Step ReduceAnd
    progress (And (B n) r) | (Stop B) | (Step step)
      = Step (SimplifyAndR B step)
  progress (And l r) | (Step step)
    = Step (SimplifyAndL step)

progress (Eq l r) with (progress l)
  progress (Eq (B n) r) | (Stop B) with (progress r)
    progress (Eq (B n) (B m)) | (Stop B) | (Stop B)
      = Step ReduceEqBool
    progress (Eq (B n) r) | (Stop B) | (Step step)
      = Step (SimplifyEqR B step)
  progress (Eq l r) | (Step step)
    = Step (SimplifyEqL step)

progress (Eq l r) with (progress l)
  progress (Eq (S n) r) | (Stop S) with (progress r)
    progress (Eq (S n) (S m)) | (Stop S) | (Stop S)
      = Step ReduceEqString
    progress (Eq (S n) r) | (Stop S) | (Step step)
      = Step (SimplifyEqR S step)
  progress (Eq l r) | (Step step)
    = Step (SimplifyEqL step)

progress (Or l r) with (progress l)
  progress (Or (B n) r) | (Stop B) with (progress r)
    progress (Or (B n) (B m)) | (Stop B) | (Stop B)
      = Step ReduceOr
    progress (Or (B n) r) | (Stop B) | (Step step)
      = Step (SimplifyOrR B step)
  progress (Or l r) | (Step step)
    = Step (SimplifyOrL step)

progress (Let this body) with (progress this)
  progress (Let this body) | (Stop value)
    = Step (ReduceLet value)
  progress (Let this body) | (Step step)
    = Step (SimplifyLet step)