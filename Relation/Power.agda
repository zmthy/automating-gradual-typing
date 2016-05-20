module Relation.Power where

open import Level
  using ( _⊔_ )

open import Relation.Binary
  using ( REL ; Rel )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl )

open import Relation.Unary
  using ( Pred ; _∈_ )

data ℙ-Pred {a ℓ f} {A : Set a}
            (P : Pred A ℓ)
            (F : Pred A f) : Set (a ⊔ ℓ ⊔ f) where
  raise : ∀ {x} → x ∈ F → P x → ℙ-Pred P F

data ℙ-REL {a b ℓ f g} {A : Set a} {B : Set b}
           (P : REL A B ℓ)
           (F : Pred A f) (G : Pred B g) : Set (a ⊔ b ⊔ ℓ ⊔ f ⊔ g) where
  raise : ∀ {x y} → x ∈ F → y ∈ G → P x y → ℙ-REL P F G

ℙ-Rel : ∀ {a ℓ f} {A : Set a} → Rel A ℓ → (F G : Pred A f) → Set (a ⊔ ℓ ⊔ f)
ℙ-Rel P F G = ℙ-REL P F G
