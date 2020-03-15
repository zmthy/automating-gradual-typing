open import Category.UnitFunctor
  using ( UnitFunctor )

module Language.Abstract (unit-functor : UnitFunctor) where

open import Category.Endofunctor
  using ( Functor ; lift )

open import Data.Bool
  using ()
  renaming ( Bool to 𝔹 )

open import Data.Fin
  using ( Fin )

open import Data.Integer
  using ( ℤ )

open import Data.Nat
  using ( ℕ ; suc )

open import Data.Vec
  using ( Vec ; _∷_ ; lookup )

open import Relation.Binary
  using ( Rel )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ )

open import Type.Abstract
  using ( Concretisation ; μTransMap )


{-# NO_POSITIVITY_CHECK #-}
data μType (F : Set → Set) : Set where
  Int : μType F
  Bool : μType F
  _➔_ : (T₁ T₂ : F (μType F)) → μType F

private

  {-# TERMINATING #-}
  map : μTransMap μType
  map f Int = Int
  map f Bool = Bool
  map f (T₁ ➔ T₂) = f (lift (map f) T₁) ➔ f (lift (map f) T₂)

  open UnitFunctor unit-functor

  concretisation : Concretisation map
  Concretisation.F concretisation = Carrier

open Concretisation concretisation
  using ( Type ; FType ; rec ; rel )
  public

open Concretisation concretisation
  using ( FRel )

_≈_ : Rel FType _
_≈_ = FRel _≡_


data _≈_⊓_ (T₁ T₂ T₃ : FType) : Set where
  rel : T₁ ≈ T₂ → T₁ ≈ T₃ → T₁ ≈ T₂ ⊓ T₃

data _≈-dom_ (T₁ T₂ : FType) : Set where
  rel : ∀ {T₃} → T₂ ≈ unit (T₁ ➔ T₃) → T₁ ≈-dom T₂

data _≈-cod_ (T₁ T₂ : FType) : Set where
  rel : ∀ {T₃} → T₂ ≈ unit (T₃ ➔ T₁) → T₁ ≈-cod T₂

data Term (n : ℕ) : Set where
  int : (x : ℤ) → Term n
  bool : (x : 𝔹) → Term n
  var : (i : Fin n) → Term n
  abs : (T : FType) (t : Term (suc n)) → Term n
  _∙_ : (t₁ t₂ : Term n) → Term n
  _+_ : (t₁ t₂ : Term n) → Term n
  if_then_else_ : (t₁ t₂ t₃ : Term n) → Term n
  _∶_ : (t : Term n) (T : FType) → Term n

data _⊢_∶_ {n} (Γ : Vec FType n) : Term n → FType → Set where
  int : ∀ {x} → Γ ⊢ int x ∶ unit Int
  bool : ∀ {x} → Γ ⊢ bool x ∶ unit Bool
  var : ∀ {i} → Γ ⊢ var i ∶ lookup Γ i
  abs : ∀ {T₁ T₂ t} → (T₁ ∷ Γ) ⊢ t ∶ T₂ → Γ ⊢ abs T₁ t ∶ unit (T₁ ➔ T₂)
  app : ∀ {T₁ T₂ T₃ t₁ t₂}
        → Γ ⊢ t₁ ∶ T₁ → Γ ⊢ t₂ ∶ T₂ → T₂ ≈-dom T₁ → T₃ ≈-cod T₁
        → Γ ⊢ (t₁ ∙ t₂) ∶ T₃
  add : ∀ {T₁ T₂ t₁ t₂}
        → Γ ⊢ t₁ ∶ T₁ → Γ ⊢ t₂ ∶ T₂ → T₁ ≈ unit Int → T₂ ≈ unit Int
        → Γ ⊢ (t₁ + t₂) ∶ unit Int
  cond : ∀ {T₁ T₂ T₃ T₄ t₁ t₂ t₃}
          → Γ ⊢ t₁ ∶ T₁ → Γ ⊢ t₂ ∶ T₂ → Γ ⊢ t₃ ∶ T₃
          → T₁ ≈ unit Bool → T₄ ≈ T₂ ⊓ T₃
          → Γ ⊢ if t₁ then t₂ else t₃ ∶ T₄
  cast : ∀ {T₁ T₂ t} → Γ ⊢ t ∶ T₁ → T₁ ≈ T₂ → Γ ⊢ (t ∶ T₂) ∶ T₂
