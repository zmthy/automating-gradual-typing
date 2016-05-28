module Type.Gradual where

open import Category.Endofunctor
  using ( Functor ; module Constant )

open import Category.UnitFunctor
  using ( UnitFunctor ; module Identity )

open import Data.Bool
  as Bool
  using ()
  renaming ( Bool to 𝔹 )

open import Data.Fin
  using ( Fin ; zero ; suc )

open import Data.Integer
  as Int
  using ( ℤ ; +_ )

open import Data.Nat
  using ( ℕ ; zero ; suc )

open import Data.Product
  using ( Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; ,_ ; uncurry )

open import Data.Vec
  using ( Vec ; [] ; _∷_ ; lookup )

open import Function
  using ( id ; _∘_ )

open import Level
  using ( _⊔_ )
  renaming ( zero to lzero ; suc to lsuc )

open import Relation.Binary
  using ( REL ; Rel )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl )

open import Relation.Power
  using ( ℙ-Pred ; ℙ-Rel ; raise )

open import Relation.Unary
  using ( Pred )

open import Relation.Unary.PredicateTransformer
  using ( PT )

record RecNatTrans {a} : Set (lsuc a) where
  field
    Type : (Set a → Set a) → Set a
    map : ∀ {F G} ⦃ _ : Functor F ⦄ → (F (Type G) → G (Type G)) → Type F → Type G

module Gradual {a} (t : RecNatTrans {a}) where

  open RecNatTrans t
    using ( map )
    renaming ( Type to RecType )

  data Maybe {a} (A : Set a) : Set a where
    ¿ : Maybe A
    type : A → Maybe A

  functor : UnitFunctor {a}
  functor = record
    { Carrier = Maybe
    ; functor = record
      { lift = λ { f ¿ → ¿ ; f (type x) → type (f x) }
      ; identity = λ { ¿ → refl ; (type x) → refl }
      ; composition = λ { ¿ → refl ; (type x) → refl }
      }
    ; unit = type
    ; lift-unit = refl
    }

  Type = RecType id
  GType = Maybe (RecType Maybe)

  {-# NO_POSITIVITY_CHECK #-}
  data γ : REL GType Type a where
    ¿ : ∀ {T} → γ ¿ T
    type : (T : RecType (λ _ → Σ (GType × Type) (uncurry γ)))
           → γ (type (map ⦃ Constant.functor _ ⦄ (proj₁ ∘ proj₁) T))
               (map ⦃ Constant.functor _ ⦄ (proj₂ ∘ proj₁) T)

  GPred : ∀ {ℓ} → PT Type GType ℓ (ℓ ⊔ a)
  GPred P T = ℙ-Pred P (γ T)

  GRel : ∀ {ℓ} → Rel Type ℓ → Rel GType (ℓ ⊔ a)
  GRel P T₁ T₂ = ℙ-Rel P (γ T₁) (γ T₂)

module ATFL where

  module _ where

    open Functor
      using ( lift )

    open UnitFunctor
      using ( Carrier )

    {-# NO_POSITIVITY_CHECK #-}
    data RecType (F : Set → Set) : Set where
      Int : RecType F
      Bool : RecType F
      _➔_ : (T₁ T₂ : F (RecType F)) → RecType F

    {-# TERMINATING #-}
    map : ∀ {F G} ⦃ _ : Functor F ⦄ → (F (RecType G) → G (RecType G))
          → RecType F → RecType G
    map ⦃ F ⦄ f Int = Int
    map ⦃ F ⦄ f Bool = Bool
    map ⦃ F ⦄ f (T₁ ➔ T₂) = f (lift F (map f) T₁) ➔ f (lift F (map f) T₂)

  type : RecNatTrans
  type = record
    { Type = RecType
    ; map = map
    }

  record Language (functor : UnitFunctor) : Set₁ where

    open UnitFunctor functor

    Type = Carrier (RecType Carrier)

    field
      _≈_ : Rel Type lzero

    data _≈_⊓_ (T₁ T₂ T₃ : Type) : Set where
      rel : T₁ ≈ T₂ → T₁ ≈ T₃ → T₁ ≈ T₂ ⊓ T₃

    data _≈-dom_ (T₁ T₂ : Type) : Set where
      rel : ∀ {T₃} → T₂ ≈ unit (T₁ ➔ T₃) → T₁ ≈-dom T₂

    data _≈-cod_ (T₁ T₂ : Type) : Set where
      rel : ∀ {T₃} → T₂ ≈ unit (T₃ ➔ T₁) → T₁ ≈-cod T₂

    data Term (n : ℕ) : Set where
      int : (x : ℤ) → Term n
      bool : (x : 𝔹) → Term n
      var : (i : Fin n) → Term n
      abs : (T : Type) (t : Term (suc n)) → Term n
      _∙_ : (t₁ t₂ : Term n) → Term n
      _+_ : (t₁ t₂ : Term n) → Term n
      if_then_else_ : (t₁ t₂ t₃ : Term n) → Term n
      _∶_ : (t : Term n) (T : Type) → Term n

    data _⊢_∶_ {n} (Γ : Vec Type n) : Term n → Type → Set where
      int : ∀ {x} → Γ ⊢ int x ∶ unit Int
      bool : ∀ {x} → Γ ⊢ bool x ∶ unit Bool
      var : ∀ {i T} → T ≡ lookup i Γ → Γ ⊢ var i ∶ T
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

open UnitFunctor
  using ( Carrier ; unit )

module STFL where

  open ATFL.Language {functor = Identity.functor} record
    { _≈_ = _≡_
    } public

module GTFL where

  open ATFL
    hiding ( type )

  open Gradual ATFL.type
    using ( ¿ ; type ; GRel )
    renaming ( functor to gradual )

  open Language {functor = gradual} record
    { _≈_ = GRel _≡_
    } public
    renaming ( _≈_ to _~_ )

  ~-example : type (type Int ➔ ¿) ~ type (¿ ➔ type Bool)
  ~-example = raise (type (((, type Int) ➔ (, ¿))))
                    (type ((, ¿) ➔ (, type Bool)))
                    refl

  term-example : Term 0
  term-example = abs ¿ (var zero ∶ type Int)

  typed-example : [] ⊢ term-example ∶ type (¿ ➔ type Int)
  typed-example = abs (cast (var refl) (raise ¿ (type Int) refl))
