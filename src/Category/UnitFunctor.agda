module Category.UnitFunctor where

open import Category.Endofunctor
  as Endofunctor
  using ( Functor )

open import Data.List
  using ( List ; [_] )
  hiding ( module List )

open import Data.Maybe
  using ( Maybe ; just ; nothing )
  hiding ( module Maybe )

open import Data.Product
  using ( _,_ ; _×_ ; <_,_> )

open import Function
  using ( _$_ ; const ; id )

open import Level
  using ( suc ; _⊔_ )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; cong₂ )


record UnitFunctor {a b} : Set (suc (a ⊔ b)) where
  field
    Carrier : Set a → Set b
    functor : Functor Carrier

  open Functor functor public

  field
    unit : ∀ {A} (x : A) → Carrier A
    lift-unit : ∀ {A B} {f : A → B} {x} → lift f (unit x) ≡ unit (f x)

open UnitFunctor
  renaming ( functor to extends )

module Identity {a} where

  instance
    functor : UnitFunctor {a}
    Carrier   functor = id
    extends   functor = Endofunctor.Identity.functor
    unit      functor = id
    lift-unit functor = refl

module Constant {a} (A : Set a) (x : A) where

  instance
    functor : UnitFunctor
    Carrier   functor = const A
    extends   functor = Endofunctor.Constant.functor A
    unit      functor = const x
    lift-unit functor = refl

module Maybe {a} where

  instance
    functor : UnitFunctor {a}
    Carrier   functor = Maybe
    extends   functor = Endofunctor.Maybe.functor
    unit      functor = just
    lift-unit functor = refl

module List {a} where

  instance
    functor : UnitFunctor {a}
    Carrier   functor = List
    extends   functor = Endofunctor.List.functor
    unit      functor = [_]
    lift-unit functor = refl

module Product {a b} (U V : UnitFunctor {a} {b}) where

  instance
    functor : UnitFunctor
    Carrier   functor A = Carrier U A × Carrier V A
    extends   functor = Endofunctor.Product.functor (extends U) (extends V)
    unit      functor = < unit U , unit V >
    lift-unit functor = cong₂ _,_ (lift-unit U) (lift-unit V)
