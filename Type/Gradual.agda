module Type.Gradual where

open import Data.Bool
  as Bool
  using ()
  renaming ( Bool to 𝔹 )

open import Data.Integer
  as Int
  using ( ℤ )

open import Data.Nat
  using ( zero ; suc )

open import Data.Fin
  using ( Fin ; zero ; suc )

open import Data.Vec
  using ( Vec ; [] ; _∷_ ; lookup )

open import Function
  using ( id ; _∘_ )

open import Level
  using ( _⊔_ )
  renaming ( suc to lsuc )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl )

module STFL where

  data Type : Set where
    Int : Type
    Bool : Type
    _➔_ : (T₁ T₂ : Type) → Type

  data _≡_⊓_ (T : Type) : Type → Type → Set where
    refl : ∀ {T₁ T₂} → T ≡ T₁ → T ≡ T₂ → T ≡ T₁ ⊓ T₂

  data _≡-dom_ (T : Type) : Type → Set where
    refl : ∀ {T′} → T ≡-dom (T ➔ T′)

  data _≡-cod_ (T : Type) : Type → Set where
    refl : ∀ {T′} → T ≡-cod (T′ ➔ T)

  data Term {n} (Γ : Vec Type n) : Type → Set where
    int : (x : ℤ) → Term Γ Int
    bool : (x : 𝔹) → Term Γ Bool
    var : ∀ {T} (i : Fin n) → T ≡ lookup i Γ → Term Γ T
    abs : (T₁ : Type) {T₂ : Type} (t : Term (T₁ ∷ Γ) T₂) → Term Γ (T₁ ➔ T₂)
    _∙_ : ∀ {T₁ T₂ T₃}
          → (t₁ : Term Γ T₁) (t₂ : Term Γ T₂)
          → T₂ ≡-dom T₁ → T₃ ≡-cod T₁
          → Term Γ T₃
    _+_ : (t₁ t₂ : Term Γ Int) → Term Γ Int
    if_then_else_ : ∀ {T₁ T₂ T₃ T₄}
                    → (t₁ : Term Γ T₁) (t₂ : Term Γ T₂) (t₃ : Term Γ T₃)
                    → T₁ ≡ Bool → T₄ ≡ T₂ ⊓ T₃
                    → Term Γ T₄
    _∶_ : ∀ {T₁} (t : Term Γ T₁) (T₂ : Type) → T₁ ≡ T₂ → Term Γ T₂

  ⟦_⟧ : Type → Set
  ⟦ Int ⟧ = ℤ
  ⟦ Bool ⟧ = 𝔹
  ⟦ T₁ ➔ T₂ ⟧ = ⟦ T₁ ⟧ → ⟦ T₂ ⟧

  data Env : ∀ {n} → Vec Type n → Set where
    [] : Env []
    _∷_ : ∀ {n T} {Γ : Vec Type n} → ⟦ T ⟧ → Env Γ → Env (T ∷ Γ)

  fetch : ∀ {n} {Γ : Vec Type n} → (i : Fin n) → Env Γ → ⟦ lookup i Γ ⟧
  fetch () []
  fetch zero (x ∷ e) = x
  fetch (suc i) (x ∷ e) = fetch i e

  eval : ∀ {n A} {Γ : Vec Type n} → Env Γ → Term Γ A → ⟦ A ⟧
  eval e (int x) = x
  eval e (bool x) = x
  eval e (var i refl) = fetch i e
  eval e (abs T t) = λ x → eval (x ∷ e) t
  eval e ((t₁ ∙ t₂) refl refl) = (eval e t₁) (eval e t₂)
  eval e (t₁ + t₂) = eval e t₁ Int.+ eval e t₂
  eval e ((if t₁ then t₂ else t₃) refl (refl refl refl)) =
    Bool.if (eval e t₁) then (eval e t₂) else (eval e t₃)
  eval e ((t ∶ T) refl) = eval e t

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field
    lift : ∀ {A B} (f : A → B) (x : F A) → F B
    identity : ∀ {A} x → lift {A} id x ≡ id x
    composition : ∀ {A B C} {f : A → B} {g : B → C} x
                  → lift (g ∘ f) x ≡ (lift g ∘ lift f) x

record UnitFunctor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field
    functor : Functor F

  open Functor functor public

  field
    unit : ∀ {A} (x : A) → F A
    lift-unit : ∀ {A B} {f : A → B} {x} → lift f (unit x) ≡ unit (f x)

module Power where

  ℙ : ∀ {a} (A : Set a) → Set (lsuc a)
  ℙ {a} A = A → Set a

  data Unary {ℓ} {A B : Set ℓ} (f : A → B) : ℙ A → ℙ B where
    raise : ∀ {F} x → F x → Unary f F (f x)

  data Binary {ℓ} {A B C : Set ℓ} (f : A → B → C) : ℙ A → ℙ B → ℙ C where
    raise : ∀ {F G} x y → F x → G y → Binary f F G (f x y)

  data Trinary {ℓ} {A B C D : Set ℓ} (f : A → B → C → D) : ℙ A → ℙ B → ℙ C → ℙ D where
    raise : ∀ {F G H} x y z → F x → G y → H z → Trinary f F G H (f x y z)

open Power

module GTFL {F : Set → Set} (U : UnitFunctor F) where

  open UnitFunctor U

  {-# NO_POSITIVITY_CHECK #-}
  data Type : Set where
    Int : Type
    Bool : Type
    _➔_ : (T₁ T₂ : F Type) → Type

  record Language : Set₁ where
    field
      _≈_ : ∀ {A : Set} → A → A → Set

    data _≈_⊓_ : F Type → F Type → F Type → Set where

    data _≈-dom_ (T : F Type) : F Type → Set where
      rel : ∀ {T′} → T ≈-dom (unit (T ➔ T′))

    data _≈-cod_ (T : F Type) : F Type → Set where
      rel : ∀ {T′} →  T ≈-cod (unit (T′ ➔ T))

    data Term {n} (Γ : Vec (F Type) n) : F Type → Set where
      int : (x : ℤ) → Term Γ (unit Int)
      bool : (x : 𝔹) → Term Γ (unit Bool)
      var : ∀ {T} (i : Fin n) → T ≡ lookup i Γ → Term Γ T
      abs : (T₁ : F Type) {T₂ : F Type} (t : Term (T₁ ∷ Γ) T₂)
            → Term Γ (unit (T₁ ➔ T₂))
      _∙_ : ∀ {T₁ T₂ T₃}
            → (t₁ : Term Γ T₁) (t₂ : Term Γ T₂)
            → T₂ ≈-dom T₁ → T₃ ≈-cod T₁
            → Term Γ T₃
      _+_ : ∀ {T₁ T₂}
            → (t₁ : Term Γ T₁) (t₂ : Term Γ T₂)
            → T₁ ≈ unit Int → T₂ ≈ unit Int
            → Term Γ (unit Int)
      if_then_else_ : ∀ {T₁ T₂ T₃ T₄}
                      → (t₁ : Term Γ T₁) (t₂ : Term Γ T₁) (t₃ : Term Γ T₁)
                      → T₁ ≈ unit Bool → T₄ ≈ T₂ ⊓ T₃
                      → Term Γ T₄
      _∶_ : ∀ {T₁} (t : Term Γ T₁) (T₂ : F Type) → T₁ ≈ T₂ → Term Γ T₂

module Identity where

  data Identity {a} (A : Set a) : Set a where
    identity : A → Identity A

  IFunctor : ∀ {a} → UnitFunctor {a} Identity
  IFunctor = record
    { functor = record
      { lift = λ { f (identity x) → identity (f x) }
      ; identity = λ { (identity x) → refl }
      ; composition = λ { (identity x) → refl }
      }
    ; unit = identity
    ; lift-unit = refl
    }

open Identity

module IType where

  open GTFL IFunctor public

  open Language record
    { _≈_ = _≡_
    } public

module GType where

  data GType A : Set where
    ¿ : GType A
    type : A → GType A

  data All {A} (P : A → Set) : ℙ (GType A) where
    ¿ : All P ¿
    type : ∀ {T} → P T → All P (type T)

  GFunctor : UnitFunctor GType
  GFunctor = record
    { functor = record
      { lift = λ { f ¿ → ¿ ; f (type x) → type (f x) }
      ; identity = λ { ¿ → refl ; (type x) → refl }
      ; composition = λ { ¿ → refl ; (type x) → refl }
      }
    ; unit = type
    ; lift-unit = refl
    }

  open GTFL GFunctor public

open GType
  using ( type )

embed : IType.Type → GType.Type
embed IType.Int = GType.Int
embed IType.Bool = GType.Bool
embed (identity T₁ IType.➔ identity T₂) = type (embed T₁) GType.➔ type (embed T₂)
