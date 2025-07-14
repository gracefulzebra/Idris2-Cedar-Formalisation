module Formalisation.Evaluation

--Deps =====================
import public Data.Fuel 

import Formalisation.Terms 
import Formalisation.Value
import Formalisation.Progress

%default total
--Deps =====================

public export
data Reduces : (this,that : Term ctxt type)
                          -> Type
  where 
    Nil : Reduces this this

    (::) : Reduce  this that
        -> Reduces      that end
        -> Reduces this      end

public export
data Finished : (term : Term ctxt type)
                      -> Type
  where
    IsValue : Value    term
            -> Finished term

    NoFuel : Finished term

public export
data Evaluation : (term : Term Nil type)
                        -> Type
  where
    Eval : {this, that : Term Nil type}
        -> (steps  : Inf (Reduces this that))
        -> (result : Finished          that)
                  -> Evaluation   this

public export
evaluate : (fuel : Fuel)
        -> (term : Term Nil type)
                -> Evaluation term

evaluate Dry term
  = Eval Nil NoFuel

evaluate (More fuel) term with (progress term)
  evaluate (More fuel) term | (Stop value)
    = Eval Nil (IsValue value)

  evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
    evaluate (More fuel) term | (Step step {that = that}) | (Eval steps result)
      = Eval (step :: steps) result