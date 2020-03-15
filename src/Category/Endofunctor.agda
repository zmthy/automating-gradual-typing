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
  using ( id ; const ; _∘_ )

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

module Identity {a} where

  open Functor

  instance
    functor : Functor {a} id
    lift        functor = id
    identity    functor x = refl
    composition functor x = refl

module Constant {a} (A : Set a) where

  open Functor

  instance
    functor : Functor {a} (const A)
    lift        functor = const id
    identity    functor x = refl
    composition functor x = refl

module Maybe {a} where

  open Functor

  instance
    functor : Functor {a} Maybe
    lift        functor = Data.Maybe.map
    identity    functor (just x) = refl
    identity    functor nothing  = refl
    composition functor (just x) = refl
    composition functor nothing  = refl

module List {a} where

  open Functor

  instance
    functor : Functor {a} List
    lift        functor = Data.List.map
    identity    functor []       = refl
    identity    functor (x ∷ xs) = cong₂ _∷_ refl (identity functor xs)
    composition functor []       = refl
    composition functor (x ∷ xs) = cong₂ _∷_ refl (composition functor xs)

module Product {a b} {F G : Set a → Set b} (f : Functor F) (g : Functor G) where

  open Functor

  instance
    functor : Functor λ A → F A × G A
    lift        functor h       = Data.Product.map (lift f h) (lift g h)
    identity    functor (x , y) = cong₂ _,_ (identity f x) (identity g y)
    composition functor (x , y) = cong₂ _,_ (composition f x) (composition g y)

open Functor ⦃...⦄ public
