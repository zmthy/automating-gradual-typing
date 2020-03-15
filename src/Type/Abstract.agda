module Type.Abstract where

open import Category.Endofunctor
  using ( Functor ; module Constant ; lift )

open import Data.Product
  using ( Σ ; Σ-syntax ; proj₁ )

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


μTrans : ∀ ℓ → Set (suc ℓ)
μTrans ℓ = (Set ℓ → Set ℓ) → Set ℓ

μTransMap : ∀ {ℓ} → μTrans ℓ → Set (suc ℓ)
μTransMap T = ∀ {F G} ⦃ _ : Functor F ⦄
              → (F (T G) → G (T G)) → T F → T G

{-# NO_POSITIVITY_CHECK #-}
record Concretisation {a} {μType : μTrans a} (map : μTransMap μType) : Set (suc a) where
  field
    F : Set a → Set a
    instance
      ⦃ functor ⦄ : Functor F

  Type = μType id
  FType = F (μType F)

  data γ : REL FType Type a

  record μγ : Set a where
    inductive
    constructor rec
    field
      {abstract-type} : FType
      {concrete-type} : Type
      concretisation : γ abstract-type concrete-type

  open μγ
    public

  γType = μType (const μγ)

  open Constant μγ

  data γ where
    rel : ∀ {T}
          → (f : F (Σ[ U ∈ γType ] map concrete-type U ≡ T))
          → γ (lift (map abstract-type ∘ proj₁) f) T

  FPred : ∀ {ℓ} → PT Type FType ℓ (ℓ ⊔ a)
  FPred P T = ℙ-Pred P (γ T)

  FRel : ∀ {ℓ} → Rel Type ℓ → Rel FType (ℓ ⊔ a)
  FRel P T₁ T₂ = ℙ-Rel P (γ T₁) (γ T₂)
