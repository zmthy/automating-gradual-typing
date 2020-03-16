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
  using ( Level ; suc ; _⊔_ )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; cong₂ )

open import Size
  using ( Size )


variable
  a b : Level

SizedSet : ∀ ℓ → Set (suc ℓ)
SizedSet ℓ = Size → Set ℓ

record Functor (F : SizedSet a → SizedSet b) : Set (suc a ⊔ b) where
  field
    lift : ∀ {A B i} → (A i → B i) → F A i → F B i
    identity : ∀ {A i} x → lift {A} {i = i} id x ≡ x
    composition : ∀ {A B C : SizedSet a} {i} {f : A i → B i} {g : B i → C i} x
                  → lift {A} {C} (g ∘ f) x ≡ (lift {B} {C} g ∘ lift {A} {B} f) x

open Functor

module Identity where

  instance
    functor : Functor {a} id
    lift        functor = id
    identity    functor x = refl
    composition functor x = refl

module Constant (A : SizedSet a) where

  instance
    functor : Functor {a} (const A)
    lift        functor = const id
    identity    functor x = refl
    composition functor x = refl

module Maybe where

  instance
    functor : Functor {a} λ A i → Maybe (A i)
    lift        functor = Data.Maybe.map
    identity    functor (just x) = refl
    identity    functor nothing  = refl
    composition functor (just x) = refl
    composition functor nothing  = refl

module List where

  instance
    functor : Functor {a} λ A i → List (A i)
    lift        functor = Data.List.map
    identity    functor     []       = refl
    identity    functor {A} (x ∷ xs) = cong₂ _∷_ refl (identity functor {A} xs)
    composition functor             []       = refl
    composition functor {A} {B} {C} (x ∷ xs) = cong₂ _∷_ refl (composition functor {A} {B} {C} xs)

module Product {F G : SizedSet a → SizedSet b} (f : Functor F) (g : Functor G) where

  instance
    functor : Functor λ A i → F A i × G A i
    lift        functor h       = Data.Product.map (lift f h) (lift g h)
    identity    functor (x , y) = cong₂ _,_ (identity f x) (identity g y)
    composition functor (x , y) = cong₂ _,_ (composition f x) (composition g y)

open Functor ⦃...⦄
  public
