module Language.List where

open import Category.UnitFunctor
  using ( module List )

open import Data.List
  using ( List ; [] ; _∷_ ; [_] )
  public

open import Data.Fin
  using ( zero )

open import Data.Product
  using ( _,_ ; -,_ )

open import Data.Vec
  using ( [] )

import Language.Abstract
open Language.Abstract.Language List
  public

open import Relation.Binary.PropositionalEquality
  using ( refl )

open import Relation.Power
  using ( raise )


≈-example : [ [ Int ] ➔ [] ] ≈ [ [] ➔ [ Bool ] ]
≈-example = raise refl
                  (rel [ rec (rel [ (-, refl) ]) ➔ rec (rel []) , refl ])
                  (rel [ rec (rel []) ➔ rec (rel [ (-, refl ) ]) , refl ])

term-example : Term 0
term-example = abs [] (var zero ∶ [ Int ])

typed-example : [] ⊢ term-example ∶ [ [] ➔ [ Int ] ]
typed-example = abs (cast var (raise refl (rel []) (rel [ (-, refl) ])))
