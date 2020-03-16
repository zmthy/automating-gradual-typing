module Type.Abstract where

open import Category.Endofunctor
  using ( Functor ; SizedSet ; module Constant ; lift )

open import Data.Product
  using ( Σ ; Σ-syntax ; proj₁ )

open import Function
  using ( const ; id ; _∘_ )

open import Level
  using ( Level ; _⊔_ ; suc )

open import Relation.Binary
  using ( REL ; Rel )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ )

open import Relation.Power
  using ( ℙ-Pred ; ℙ-Rel )

open import Relation.Unary.PredicateTransformer
  using ( PT )

open import Size
  using ( Size ; Size<_ )


variable
  a ℓ : Level

μTrans : ∀ ℓ → Set (suc ℓ)
μTrans ℓ = (SizedSet ℓ → SizedSet ℓ) → SizedSet ℓ

μTransMap : μTrans ℓ → Set (suc ℓ)
μTransMap T = ∀ {F G} ⦃ _ : Functor F ⦄
              → {i : Size}
              → (∀ {j : Size< i} → F (T G) j → G (T G) j) → T F i → T G i

{-# NO_POSITIVITY_CHECK #-}
record Concretisation {μType : μTrans a} (map : μTransMap μType) : Set (suc a) where
  field
    F : SizedSet a → SizedSet a
    instance
      ⦃ functor ⦄ : Functor F

  module Types (i : Size) where
    Type = μType id i
    FType = F (μType F) i

  open Types

  data γ {i : Size} : REL (FType i) (Type i) a

  record μγ (i : Size) : Set a where
    inductive
    constructor rec
    field
      {abstract-type} : FType i
      {concrete-type} : Type i
      concretisation : γ abstract-type concrete-type

  open μγ
    public

  γType = μType (const μγ)

  open Constant μγ

  Tγ : (i : Size) → Type i → Size → Set a
  Tγ i T _ = Σ[ U ∈ γType i ] map concrete-type U ≡ T

  data γ {i} where
    rel : ∀ {T : Type i}
          → (f : F (Tγ i T) i)
          → γ (lift {B = μType F} (map abstract-type ∘ proj₁) f) T

  variable
    i : Size

  FPred : PT (Type i) (FType i) ℓ (ℓ ⊔ a)
  FPred P T = ℙ-Pred P (γ T)

  FRel : Rel (Type i) ℓ → Rel (FType i) (ℓ ⊔ a)
  FRel P T₁ T₂ = ℙ-Rel P (γ T₁) (γ T₂)
