module Category.UnitFunctor where

open import Data.Product
  using ( _,_ ; _×_ ; <_,_> ; map ; uncurry )

open import Function
  using ( _$_ ; id ; _∘_ )

open import Level
  using ( suc ; _⊔_ )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; cong₂ )

record Functor {a b} (F : Set a → Set b) : Set (suc a ⊔ b) where
  field
    lift : ∀ {A B} → (A → B) → F A → F B
    identity : ∀ {A} x → lift {A} id x ≡ id x
    composition : ∀ {A B C} {f : A → B} {g : B → C} x
                  → lift (g ∘ f) x ≡ (lift g ∘ lift f) x

record UnitFunctor {a b} : Set (suc (a ⊔ b)) where
  field
    Carrier : Set a → Set b
    functor : Functor Carrier

  open Functor functor public

  field
    unit : ∀ {A} (x : A) → Carrier A
    lift-unit : ∀ {A B} {f : A → B} {x} → lift f (unit x) ≡ unit (f x)

module Identity where

  functor : ∀ {a} → UnitFunctor {a}
  functor = record
    { Carrier = id
    ; functor = record
      { lift = _$_
      ; identity = λ _ → refl
      ; composition = λ _ → refl
      }
    ; unit = id
    ; lift-unit = refl
    }

module Product {a b} (U V : UnitFunctor {a} {b}) where

  open UnitFunctor
    hiding ( functor )

  F : Set a → Set b
  F A = Carrier U A × Carrier V A

  functor : UnitFunctor {a} {b}
  functor = record
    { Carrier = λ A → F A
    ; functor = record
      { lift = λ f → map (lift U f) (lift V f)
      ; identity = λ { (x , y) → cong₂ _,_ (identity U x) (identity V y) }
      ; composition = λ { (x , y) → cong₂ _,_ (composition U x) (composition V y) }
      }
    ; unit = < unit U , unit V >
    ; lift-unit = cong₂ _,_ (lift-unit U) (lift-unit V)
    }
