module Language.List where

open import Category.UnitFunctor
  using ( module List )

open import Data.List
  using ( [] ; [_] )

open import Data.Fin
  using ( zero )

open import Data.Product
  using ( _,_ ; ,_ )

open import Data.Vec
  using ( [] )

open import Language.Abstract List.functor
  public

open import Relation.Binary.PropositionalEquality
  using ( refl )

open import Relation.Power
  using ( raise )


≈-example : [ [ Int ] ➔ [] ] ≈ [ [] ➔ [ Bool ] ]
≈-example = raise refl
                  (rel [ ((, rel [ (, refl) ]) ➔ (, rel [])) , refl ])
                  (rel [ ((, rel []) ➔ (, rel [ (, refl ) ])) , refl ])

term-example : Term 0
term-example = abs [] (var zero ∶ [ Int ])

typed-example : [] ⊢ term-example ∶ [ [] ➔ [ Int ] ]
typed-example = abs (cast (var refl) (raise refl (rel []) (rel [ (, refl) ])))
