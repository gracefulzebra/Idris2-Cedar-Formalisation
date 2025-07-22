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
    SimplifyEqBoolL  : Reduce          this that
                    -> Reduce (EqBool  this      right)
                              (EqBool       that right)

    SimplifyEqBoolR  : Value          left
                    -> Reduce              this that
                    -> Reduce (EqBool left this      )
                              (EqBool left      that )

    SimplifyEqStringL  : Reduce            this that
                      -> Reduce (EqString  this      right)
                                (EqString       that right)

    SimplifyEqStringR  : Value            left
                      -> Reduce                this that
                      -> Reduce (EqString left this      )
                                (EqString left      that )

    SimplifyEqERefL : Reduce          this that
                   -> Reduce (EqERef  this      right)
                             (EqERef       that right)

    SimplifyEqERefR : Value          left
                   -> Reduce              this that
                   -> Reduce (EqERef left this      )
                             (EqERef left      that )

    ReduceEqBool : Reduce (EqBool (B a) (B b))
                          (B  ( a  ==  b ))

    ReduceEqString : Reduce (EqString (S a) (S b))
                            (B  ( a  == b ))

    ReduceEqERef : Reduce (EqERef (ERef id1 (S t1)) (ERef id2 (S t2)))
                          (B    ((id1 == id2) && (t1 == t2)))

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
progress (ERef identity (S tag)) = Stop (ERef {identity} {tag})

progress (And l r) with (progress l)
  progress (And (B n) r) | (Stop B) with (progress r)
    progress (And (B n) (B m)) | (Stop B) | (Stop B)
      = Step ReduceAnd
    progress (And (B n) r) | (Stop B) | (Step step)
      = Step (SimplifyAndR B step)
  progress (And l r) | (Step step)
    = Step (SimplifyAndL step)

progress (EqBool l r) with (progress l)
  progress (EqBool (B n) r) | (Stop B) with (progress r)
    progress (EqBool (B n) (B m)) | (Stop B) | (Stop B)
      = Step ReduceEqBool
    progress (EqBool (B n) r) | (Stop B) | (Step step)
      = Step (SimplifyEqBoolR B step)
  progress (EqBool l r) | (Step step)
    = Step (SimplifyEqBoolL step)

progress (EqString l r) with (progress l)
  progress (EqString (S n) r) | (Stop S) with (progress r)
    progress (EqString (S n) (S m)) | (Stop S) | (Stop S)
      = Step ReduceEqString
    progress (EqString (S n) r) | (Stop S) | (Step step)
      = Step (SimplifyEqStringR S step)
  progress (EqString l r) | (Step step)
    = Step (SimplifyEqStringL step)

progress (EqERef l r) with (progress l)
  progress (EqERef (ERef n) r) | (Stop ERef) with (progress r)
    progress (EqERef (ERef n) (ERef m)) | (Stop ERef) | (Stop ERef)
      = Step ReduceEqEUID
    progress (EqERef (ERef n) r) | (Stop ERef) | (Step step)
      = Step (SimplifyEqERefR ERef step)
  progress (EqERef l r) | (Step step)
    = Step (SimplifyEqEREfL step)

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