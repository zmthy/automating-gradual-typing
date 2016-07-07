module Language.Simple where

open import Category.UnitFunctor
  using ( module Identity )

open import Data.Fin
  using ( zero )

open import Data.Product
  using ( _,_ ; ,_ )

open import Data.Vec
  using ( [] )

open import Language.Abstract Identity.functor
  public

open import Relation.Binary.PropositionalEquality
  using ( refl )

open import Relation.Power
  using ( raise )

≡-example : (Int ➔ Bool) ≈ (Int ➔ Bool)
≡-example = raise refl
                  (rel (((, rel (, refl)) ➔ (, rel (, refl))) , refl))
                  (rel (((, rel (, refl)) ➔ (, rel (, refl))) , refl))

term-example : Term 0
term-example = abs Int (var zero ∶ Int)

typed-example : [] ⊢ term-example ∶ (Int ➔ Int)
typed-example = abs (cast (var refl) (raise refl (rel (, refl))
                                                 (rel (, refl))))