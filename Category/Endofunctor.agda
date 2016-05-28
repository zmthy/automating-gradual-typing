module Category.Endofunctor where

open import Data.Product
  using ( _,_ ; _×_ ; map )

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

open Functor

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

module Product {a b} {F G : Set a → Set b} (f : Functor F) (g : Functor G) where

  instance
    functor : Functor {a} {b} (λ A → F A × G A)
    functor = record
      { lift = λ h → map (lift f h) (lift g h)
      ; identity = λ { (x , y) → cong₂ _,_ (identity f x) (identity g y) }
      ; composition = λ { (x , y) → cong₂ _,_ (composition f x) (composition g y) }
      }
