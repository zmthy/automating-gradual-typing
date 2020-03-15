module Language.Gradual where

open import Category.UnitFunctor
  using ( module Maybe )

open import Data.Fin
  using ( zero )

open import Data.Maybe
  using ( just ; nothing )

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


≈-example : just (just Int ➔ nothing) ≈ just (nothing ➔ just Bool)
≈-example = raise refl
                  (rel
                    (just (((-, rel (just (-, refl))) ➔ (-, rel nothing)) , refl)))
                  (rel
                    (just (((-, rel nothing) ➔ (-, rel (just (-, refl)))) , refl)))

term-example : Term 0
term-example = abs nothing (var zero ∶ just Int)

typed-example : [] ⊢ term-example ∶ just (nothing ➔ just Int)
typed-example = abs (cast var (raise refl (rel nothing)
                                          (rel (just (-, refl)))))
