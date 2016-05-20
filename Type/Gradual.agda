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
  using ( zero ; suc )

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
    map : ∀ {F G} → Functor F → (F (Type G) → G (Type G)) → Type F → Type G

module Gradual {a} (t : RecNatTrans {a}) where

  data Type {a} (A : Set a) : Set a where
    ¿ : Type A
    type : A → Type A

  functor : UnitFunctor {a}
  functor = record
    { Carrier = Type
    ; functor = record
      { lift = λ { f ¿ → ¿ ; f (type x) → type (f x) }
      ; identity = λ { ¿ → refl ; (type x) → refl }
      ; composition = λ { ¿ → refl ; (type x) → refl }
      }
    ; unit = type
    ; lift-unit = refl
    }

  RecType = RecNatTrans.Type t
  CType = RecType id
  GType = Type (RecType Type)

  {-# NO_POSITIVITY_CHECK #-}
  data γ : REL GType CType a where
    ¿ : ∀ {T} → γ ¿ T
    type : (T : RecType (λ _ → Σ (GType × CType) (uncurry γ)))
           → γ (type (RecNatTrans.map t (Constant.functor _) (proj₁ ∘ proj₁) T))
               (RecNatTrans.map t (Constant.functor _) (proj₂ ∘ proj₁) T)

  Unary : ∀ {ℓ} → PT CType GType ℓ (ℓ ⊔ a)
  Unary P T = ℙ-Pred P (γ T)

  Binary : ∀ {ℓ} → Rel CType ℓ → Rel GType (ℓ ⊔ a)
  Binary P T₁ T₂ = ℙ-Rel P (γ T₁) (γ T₂)

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
    map : ∀ {F G} → Functor F → (F (RecType G) → G (RecType G))
          → RecType F → RecType G
    map F f Int = Int
    map F f Bool = Bool
    map F f (T₁ ➔ T₂) = f (lift F (map F f) T₁) ➔ f (lift F (map F f) T₂)

  type : RecNatTrans
  type = record
    { Type = RecType
    ; map = map
    }

  module Under (U : UnitFunctor {lzero} {lzero}) where

    open UnitFunctor U

    Type = Carrier (RecType Carrier)

    record Language : Set₁ where

      field
        _≈_ : Type → Type → Set

      data _≈_⊓_ (T : Type) : Type → Type → Set where
        rel : ∀ {T₁ T₂} → T ≈ T₁ → T ≈ T₂ → T ≈ T₁ ⊓ T₂

      data _≈-dom_ (T : Type) : Type → Set where
        rel : ∀ {T′} → T ≈-dom (unit (T ➔ T′))

      data _≈-cod_ (T : Type) : Type → Set where
        rel : ∀ {T′} → T ≈-cod (unit (T′ ➔ T))

      data Term {n} (Γ : Vec (Type) n) : Type → Set where
        int : (x : ℤ) → Term Γ (unit Int)
        bool : (x : 𝔹) → Term Γ (unit Bool)
        var : ∀ {T} (i : Fin n) → T ≡ lookup i Γ → Term Γ T
        abs : (T₁ : Type) {T₂ : Type} (t : Term (T₁ ∷ Γ) T₂)
              → Term Γ (unit (T₁ ➔ T₂))
        _∙_⊣_,_ : ∀ {T₁ T₂ T₃}
                  → (t₁ : Term Γ T₁) (t₂ : Term Γ T₂)
                  → T₂ ≈-dom T₁ → T₃ ≈-cod T₁
                  → Term Γ T₃
        _+_⊣_,_ : ∀ {T₁ T₂}
                  → (t₁ : Term Γ T₁) (t₂ : Term Γ T₂)
                  → T₁ ≈ unit Int → T₂ ≈ unit Int
                  → Term Γ (unit Int)
        if_then_else_ : ∀ {T₁ T₂ T₃ T₄}
                        → (t₁ : Term Γ T₁) (t₂ : Term Γ T₁) (t₃ : Term Γ T₁)
                        → T₁ ≈ unit Bool → T₄ ≈ T₂ ⊓ T₃
                        → Term Γ T₄
        _∶_⊣_ : ∀ {T₁} (t : Term Γ T₁) (T₂ : Type) → T₁ ≈ T₂ → Term Γ T₂

open UnitFunctor
  using ( Carrier ; unit )

module STFL where

  open ATFL.Under Identity.functor public

  open Language record
    { _≈_ = _≡_
    } public

module GTFL where

  open ATFL
    hiding ( type )

  open Gradual ATFL.type
    using ( ¿ ; type ; functor ; Binary )

  open Under functor public
    renaming ( Type to GType )

  _≅_ : Rel GType _
  _≅_ = Binary _≡_

  ≅-example : type (type Int ➔ ¿) ≅ type (¿ ➔ type Bool)
  ≅-example = raise (type ((, type Int) ➔ (, ¿)))
                    (type ((, ¿) ➔ (, type Bool)))
                    refl

  open Language record
    { _≈_ = _≅_
    } public

  term-example : Term [] ¿
  term-example = int (+ 1) ∶ ¿ ⊣ raise (type Int) ¿ refl
