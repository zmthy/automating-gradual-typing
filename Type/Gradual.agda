module Type.Gradual where

open import Category.Endofunctor
  using ( Functor
        ; module Constant
        ; module Identity
        ; module List
        ; module Maybe )

open import Category.UnitFunctor
  using ( UnitFunctor )
  renaming ( module Constant to ConstantUnit
           ; module Identity to IdentityUnit
           ; module List to ListUnit
           ; module Maybe to MaybeUnit )

open import Data.Bool
  as Bool
  using ()
  renaming ( Bool to 𝔹 )

open import Data.Fin
  using ( Fin ; zero ; suc )

open import Data.Integer
  as Int
  using ( ℤ ; +_ )

open import Data.List
  using ( [] ; [_] )

open import Data.Maybe
  using ( just ; nothing )

open import Data.Nat
  using ( ℕ ; zero ; suc )

open import Data.Product
  using ( Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; ,_ ; uncurry )

open import Data.Unit
  using ( ⊤ ; tt )

open import Data.Vec
  using ( Vec ; [] ; _∷_ ; lookup )

open import Function
  using ( const ; id ; _∘_ )

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

record Abstract {a} (t : RecNatTrans {a}) : Set (lsuc a) where
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

module ATFL (uf : UnitFunctor {lzero} {lzero}) where

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

  open UnitFunctor uf

  module Lift = Abstract {t = type} record
    { functor = functor
    }

  open Lift
    using ( Type ; FType ; rel )
    public

  open Lift
    using ( FRel )

  _≈_ : Rel FType lzero
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

  open ATFL IdentityUnit.functor public

  ≡-example : (Int ➔ Bool) ≈ (Int ➔ Bool)
  ≡-example = raise refl
                    (rel (((, rel (, refl)) ➔ (, rel (, refl))) , refl))
                    (rel (((, rel (, refl)) ➔ (, rel (, refl))) , refl))

  term-example : Term 0
  term-example = abs Int (var zero ∶ Int)

  typed-example : [] ⊢ term-example ∶ (Int ➔ Int)
  typed-example = abs (cast (var refl) (raise refl (rel (, refl))
                                                   (rel (, refl))))

module DTFL where

  open ATFL (ConstantUnit.functor ⊤ tt) public

  ≈-example : {T : Type} → tt ≈ tt
  ≈-example {T} = raise {x = T} refl (rel tt) (rel tt)

  term-example : Term 0
  term-example = abs tt (var zero ∶ tt)

  typed-example : {T : Type} → [] ⊢ term-example ∶ tt
  typed-example {T} = abs (cast (var refl) (raise {x = T} refl (rel tt) (rel tt)))

module GTFL where

  open ATFL MaybeUnit.functor public

  ≈-example : just (just Int ➔ nothing) ≈ just (nothing ➔ just Bool)
  ≈-example = raise refl
                    (rel
                      (just
                        (((, rel (just (, refl))) ➔ (, rel nothing)) , refl)))
                    (rel
                      (just
                        (((, rel nothing) ➔ (, rel (just (, refl)))) , refl)))

  term-example : Term 0
  term-example = abs nothing (var zero ∶ just Int)

  typed-example : [] ⊢ term-example ∶ just (nothing ➔ just Int)
  typed-example = abs (cast (var refl) (raise refl (rel nothing)
                                                   (rel (just (, refl)))))

module LTFL where

  open ATFL ListUnit.functor public

  ≈-example : [ [ Int ] ➔ [] ] ≈ [ [] ➔ [ Bool ] ]
  ≈-example = raise refl
                    (rel [ ((, rel [ (, refl) ]) ➔ (, rel [])) , refl ])
                    (rel [ ((, rel []) ➔ (, rel [ (, refl ) ])) , refl ])

  term-example : Term 0
  term-example = abs [] (var zero ∶ [ Int ])

  typed-example : [] ⊢ term-example ∶ [ [] ➔ [ Int ] ]
  typed-example = abs (cast (var refl) (raise refl (rel []) (rel [ (, refl) ])))
