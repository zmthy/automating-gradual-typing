module Language.Gradual where

open import Category.UnitFunctor
  using ( module Maybe )

open import Data.Fin
  using ( zero )

open import Data.Maybe
  using ()
  renaming ( just to type
           ; nothing to ??
           )
  public

open import Data.Product
  using ( _,_ ; -,_ )

open import Data.Vec
  using ( [] )

open import Language.Abstract Maybe.functor
  public

open import Relation.Binary.PropositionalEquality
  using ( refl )

open import Relation.Power
  using ( raise )


≈-example : type (type Int ➔ ??) ≈ type (?? ➔ type Bool)
≈-example = raise refl
                  (rel
                    (type (rec (rel (type (-, refl))) ➔ rec (rel ??) , refl)))
                  (rel
                    (type (rec (rel ??) ➔ rec (rel (type (-, refl))) , refl)))

term-example : Term 0
term-example = abs ?? (var zero ∶ type Int)

typed-example : [] ⊢ term-example ∶ type (?? ➔ type Int)
typed-example = abs (cast var (raise refl (rel ??)
                                          (rel (type (-, refl)))))
