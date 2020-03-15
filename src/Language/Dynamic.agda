module Language.Dynamic where

open import Category.UnitFunctor
  using ( module Constant )

open import Data.Fin
  using ( zero )

open import Data.Unit
  using ()
  renaming ( tt to ⋆ )
  public

open import Data.Vec
  using ( [] )

open import Language.Abstract (Constant.functor ⋆)
  public

open import Relation.Binary.PropositionalEquality
  using ( refl )

open import Relation.Power
  using ( raise )


≈-example : {T : Type} → ⋆ ≈ ⋆
≈-example {T} = raise {x = T} refl (rel ⋆) (rel ⋆)

term-example : Term 0
term-example = abs ⋆ (var zero ∶ ⋆)

typed-example : {T : Type} → [] ⊢ term-example ∶ ⋆
typed-example {T} = abs (cast var (raise {x = T} refl (rel ⋆) (rel ⋆)))
