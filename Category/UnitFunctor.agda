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

module Identity {a} where

  instance
    functor : UnitFunctor {a}
    functor = record
      { Carrier = id
      ; functor = Endofunctor.Identity.functor
      ; unit = id
      ; lift-unit = refl
      }

module Constant {a} (A : Set a) (x : A) where

  instance
    functor : UnitFunctor {a}
    functor = record
      { Carrier = const A
      ; functor = Endofunctor.Constant.functor A
      ; unit = const x
      ; lift-unit = refl
      }

module Maybe {a} where

  functor : UnitFunctor {a}
  functor = record
    { Carrier = Maybe
    ; functor = Endofunctor.Maybe.functor
    ; unit = just
    ; lift-unit = refl
    }

module List {a} where

  functor : UnitFunctor {a}
  functor = record
    { Carrier = List
    ; functor = Endofunctor.List.functor
    ; unit = [_]
    ; lift-unit = refl
    }

module Product {a b} (U V : UnitFunctor {a} {b}) where

  open UnitFunctor
    hiding ( functor )

  instance
    functor : UnitFunctor {a} {b}
    functor = record
      { Carrier = λ A → Carrier U A × Carrier V A
      ; functor = Endofunctor.Product.functor (UnitFunctor.functor U)
                                              (UnitFunctor.functor V)
      ; unit = < unit U , unit V >
      ; lift-unit = cong₂ _,_ (lift-unit U) (lift-unit V)
      }
