module Type.Gradual where

open import Category.UnitFunctor

open import Data.Bool
  as Bool
  using ()
  renaming ( Bool to 𝔹 )

open import Data.Fin
  using ( Fin ; zero ; suc )

open import Data.Integer
  as Int
  using ( ℤ )

open import Data.Nat
  using ( zero ; suc )

open import Data.Product
  using ( Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; uncurry )

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

open import Relation.Unary
  using ( Pred ; _∈_ )

open import Relation.Unary.PredicateTransformer
  using ( PT )

module Concrete where

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

module Gradual where

  data Type A : Set where
    ¿ : Type A
    type : A → Type A

  functor : UnitFunctor
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

open Gradual
  using ( ¿ ; type )

module Power where

  data Unary {a ℓ f} {A : Set a}
            (P : Pred A ℓ)
            (F : Pred A f) : Set (a ⊔ ℓ ⊔ f) where
    raise : ∀ x → x ∈ F → P x → Unary P F

  data Binary {a b ℓ f g} {A : Set a} {B : Set b}
              (P : REL A B ℓ)
              (F : Pred A f) (G : Pred B g) : Set (a ⊔ b ⊔ ℓ ⊔ f ⊔ g) where
    raise : ∀ x y → x ∈ F → y ∈ G → P x y → Binary P F G

open Power
  using ( raise )

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
    map : ∀ {F G} → Functor F → (f : F (RecType G) → G (RecType G))
          → RecType F → RecType G
    map F f Int = Int
    map F f Bool = Bool
    map F f (T₁ ➔ T₂) = f (lift F (map F f) T₁) ➔ f (lift F (map F f) T₂)

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
        rel : ∀ {T′} →  T ≈-cod (unit (T′ ➔ T))

      data Term {n} (Γ : Vec (Type) n) : Type → Set where
        int : (x : ℤ) → Term Γ (unit Int)
        bool : (x : 𝔹) → Term Γ (unit Bool)
        var : ∀ {T} (i : Fin n) → T ≡ lookup i Γ → Term Γ T
        abs : (T₁ : Type) {T₂ : Type} (t : Term (T₁ ∷ Γ) T₂)
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
        _∶_ : ∀ {T₁} (t : Term Γ T₁) (T₂ : Type) → T₁ ≈ T₂ → Term Γ T₂

open UnitFunctor
  using ( Carrier ; unit )

module STFL where

  open ATFL.Under Identity.functor public

  open Language record
    { _≈_ = _≡_
    } public

module GTFL where

  open ATFL

  open Under Gradual.functor public
    renaming ( Type to GType )

  open STFL
    hiding ( Language )

  open Gradual
    using ( ¿ ; type )

  ℙ : Set → Set₁
  ℙ T = Pred T _

  {-# NO_POSITIVITY_CHECK #-}
  data γ : REL GType Type lzero where
    ¿ : ∀ {T} → γ ¿ T
    type : (T : RecType (λ _ → Σ (GType × Type) (uncurry γ)))
           → γ (type (map (Constant.functor _) (proj₁ ∘ proj₁) T))
               (map (Constant.functor _) (proj₂ ∘ proj₁) T)

  Unary : ∀ {ℓ} → PT Type GType ℓ ℓ
  Unary P T = Power.Unary P (γ T)

  Binary : ∀ {ℓ} → Rel Type ℓ → Rel GType ℓ
  Binary P T₁ T₂ = Power.Binary P (γ T₁) (γ T₂)

  _≅_ : Rel GType _
  _≅_ = Binary _≡_

  example : type (type Int ➔ ¿) ≅ type (¿ ➔ type Bool)
  example = raise (Int ➔ Bool)
                  (Int ➔ Bool)
                  (type (((type Int , Int) , type Int) ➔ ((¿ , Bool) , ¿)))
                  (type (((¿ , Int) , ¿) ➔ ((type Bool , Bool) , type Bool)))
                  refl

  open Language record
    { _≈_ = _≅_
    } public
