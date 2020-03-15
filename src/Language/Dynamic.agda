module Language.Dynamic where

open import Category.UnitFunctor
  using ( module Constant )

open import Data.Fin
  using ( zero )

open import Data.Unit
  using ( ⊤ ; tt )

open import Data.Vec
  using ( [] )

open import Language.Abstract (Constant.functor ⊤ tt)
  public

open import Relation.Binary.PropositionalEquality
  using ( refl )

open import Relation.Power
  using ( raise )


≈-example : {T : Type} → tt ≈ tt
≈-example {T} = raise {x = T} refl (rel tt) (rel tt)

term-example : Term 0
term-example = abs tt (var zero ∶ tt)

typed-example : {T : Type} → [] ⊢ term-example ∶ tt
typed-example {T} = abs (cast var (raise {x = T} refl
                                         (rel tt) (rel tt)))
