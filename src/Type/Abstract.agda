module Type.Abstract where

open import Category.Endofunctor
  using ( Functor ; module Constant )

open import Data.Product
  using ( Σ ; proj₁ ; proj₂ ; _×_ ; uncurry )

open import Function
  using ( const ; id ; _∘_ )

open import Level
  using ( _⊔_ ; suc )

open import Relation.Binary
  using ( REL ; Rel )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ )

open import Relation.Power
  using ( ℙ-Pred ; ℙ-Rel )

open import Relation.Unary.PredicateTransformer
  using ( PT )

record RecNatTrans {a} : Set (suc a) where
  field
    Type : (Set a → Set a) → Set a
    map : ∀ {F G} ⦃ _ : Functor F ⦄
          → (F (Type G) → G (Type G)) → Type F → Type G

record Abstract {a} (t : RecNatTrans {a}) : Set (suc a) where
  field
    {F} : Set a → Set a
    functor : Functor F

  open Functor functor
    using ( lift )

  open RecNatTrans t
    using ( map )
    renaming ( Type to RecType )

  Type = RecType id
  FType = F (RecType F)

  {-# NO_POSITIVITY_CHECK #-}
  data γ : REL FType Type a where
    rel : ∀ {T}
          → (f : F (Σ (RecType (const (Σ (FType × Type) (uncurry γ))))
                      (_≡_ T ∘ map ⦃ Constant.functor _ ⦄ (proj₂ ∘ proj₁))))
          → γ (lift (map ⦃ Constant.functor _ ⦄ (proj₁ ∘ proj₁) ∘ proj₁) f) T

  FPred : ∀ {ℓ} → PT Type FType ℓ (ℓ ⊔ a)
  FPred P T = ℙ-Pred P (γ T)

  FRel : ∀ {ℓ} → Rel Type ℓ → Rel FType (ℓ ⊔ a)
  FRel P T₁ T₂ = ℙ-Rel P (γ T₁) (γ T₂)
