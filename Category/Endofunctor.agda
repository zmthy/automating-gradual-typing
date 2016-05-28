module Category.Endofunctor where

open import Data.List
  using ( List ; [] ; _∷_ )
  hiding ( module List )

open import Data.Maybe
  using ( Maybe ; just ; nothing )
  hiding ( module Maybe )

open import Data.Product
  using ( _,_ ; _×_ )

open import Function
  using ( _$_ ; id ; const ; _∘_ )

open import Level
  using ( suc ; _⊔_ )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; cong₂ )

record Functor {a b} (F : Set a → Set b) : Set (suc a ⊔ b) where
  field
    lift : ∀ {A B} → (A → B) → F A → F B
    identity : ∀ {A} x → lift {A} id x ≡ x
    composition : ∀ {A B C} {f : A → B} {g : B → C} x
                  → lift (g ∘ f) x ≡ (lift g ∘ lift f) x

module Identity where

  instance
    functor : ∀ {a} → Functor {a} id
    functor = record
      { lift = _$_
      ; identity = λ _ → refl
      ; composition = λ _ → refl
      }

module Constant {a} (A : Set a) where

  instance
    functor : Functor {a} (const A)
    functor = record
      { lift = const id
      ; identity = λ _ → refl
      ; composition = λ _ → refl
      }

module Maybe {a} where

  functor : Functor {a} Maybe
  functor = record
    { lift = Data.Maybe.map
    ; identity = λ { (just x) → refl ; nothing → refl }
    ; composition = λ { (just x) → refl ; nothing → refl }
    }

module List {a} where

  private
    lift : {A B : Set a} → (A → B) → List A → List B
    lift = Data.List.map

    identity : {A : Set a} (x : List A) → lift id x ≡ x
    identity [] = refl
    identity (x ∷ xs) = cong₂ _∷_ refl (identity xs)

    composition : ∀ {A B C : Set a} {f : A → B} {g : B → C} x
                  → lift (g ∘ f) x ≡ (lift g ∘ lift f) x
    composition [] = refl
    composition (x ∷ xs) = cong₂ _∷_ refl (composition xs)

  functor : Functor {a} List
  functor = record
    { lift = lift
    ; identity = identity
    ; composition = composition
    }

module Product {a b} {F G : Set a → Set b} (f : Functor F) (g : Functor G) where

  open Functor

  instance
    functor : Functor {a} {b} (λ A → F A × G A)
    functor = record
      { lift = λ h → Data.Product.map (lift f h) (lift g h)
      ; identity = λ { (x , y) → cong₂ _,_ (identity f x) (identity g y) }
      ; composition = λ { (x , y) → cong₂ _,_ (composition f x) (composition g y) }
      }
