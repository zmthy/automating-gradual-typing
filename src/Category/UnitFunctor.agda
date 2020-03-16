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
  using ( Level ; suc ; _⊔_ )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; cong₂ )


variable
  a b : Level

record UnitFunctor (F : Set a → Set b) : Set (suc (a ⊔ b)) where
  field
    instance
      functor : Functor λ A i → F (A i)

  open Functor functor public

  field
    unit : ∀ {A} (x : A) → F A
    lift-unit : ∀ {A B i} {f : A i → B i} {x} → lift {A} {B} f (unit x) ≡ unit (f x)

open UnitFunctor
  renaming ( functor to extends )

module Identity where

  instance
    functor : UnitFunctor {a} id
    extends   functor = Endofunctor.Identity.functor
    unit      functor = id
    lift-unit functor = refl

module Constant {A : Set a} (x : A) where

  instance
    functor : UnitFunctor {a} (const A)
    extends   functor = Endofunctor.Constant.functor (const A)
    unit      functor = const x
    lift-unit functor = refl

module Maybe where

  instance
    functor : UnitFunctor {a} Maybe
    extends   functor = Endofunctor.Maybe.functor
    unit      functor = just
    lift-unit functor = refl

module List where

  instance
    functor : UnitFunctor {a} List
    extends   functor = Endofunctor.List.functor
    unit      functor = [_]
    lift-unit functor = refl

module Product {F G : Set a → Set b} (u : UnitFunctor F) (v : UnitFunctor G) where

  instance
    functor : UnitFunctor λ A → F A × G A
    extends   functor = Endofunctor.Product.functor (extends u) (extends v)
    unit      functor = < unit u , unit v >
    lift-unit functor = cong₂ _,_ (lift-unit u) (lift-unit v)

open UnitFunctor
  public
