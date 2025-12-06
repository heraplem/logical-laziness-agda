module LogicalLaziness.Language.Logic.Base where

open import Agda.Builtin.FromNat
  public

open import Function
  hiding ( _∋_
         )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Unit
  public
  using ( tt
        )
open import Data.Unit
open import Data.Product
open import Data.Bool
  using ( Bool
        ; false
        ; true
        )
open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Data.T
  using ( T
        ; undefined
        ; thunk
        )
open import LogicalLaziness.Base.Data.ListA
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Base.Data.List.All.Relation.Binary.Pointwise
  as AllPointwise
  using ( []
        ; _∷_
        )
  renaming (Pointwise to AllPointwise)

infix  1.59  `_ ⇓_ #_
infixl 1.56  _`+_ _⇓+_
infixr 1.55  _`∷_ _⇓∷_
infixr 1.54  _`,_ _⇓,_
infix  1.54  _`≟_ _`≲_
infixr 1.52 _`×_
infixr 1.51  _`?_
infix  1.505 `if_`then_`else_ ⇓if_⇓then_ ⇓if_⇓else_
infix  1.50  `let_`in_ ⇓let_⇓in_

-----------
-- Types --
-----------

data Ty : Type where
  `Unit  : Ty
  `Bool  : Ty
  _`×_   : Ty → Ty → Ty
  `T     : Ty → Ty
  `ℕ     : Ty
  `ListA : Ty → Ty

variable
  α β τ τ₁ τ₂ τ₃ : Ty

------------
-- Values --
------------

⟦_⟧ᵗ : Ty → Type
⟦ `Unit    ⟧ᵗ = ⊤
⟦ `Bool    ⟧ᵗ = Bool
⟦ α `× β   ⟧ᵗ = ⟦ α ⟧ᵗ × ⟦ β ⟧ᵗ
⟦ `T α     ⟧ᵗ = T ⟦ α ⟧ᵗ
⟦ `ℕ       ⟧ᵗ = ℕ
⟦ `ListA α ⟧ᵗ = ListA ⟦ α ⟧ᵗ

--------------
-- Contexts --
--------------

Ctx : Type
Ctx = List Ty

variable
  Γ Δ Θ : Ctx

------------------
-- Environments --
------------------

⟦_⟧ᶜ : Ctx → Type
⟦_⟧ᶜ = All ⟦_⟧ᵗ

variable
  γ γ₁ γ₂ : ⟦ Γ ⟧ᶜ
  δ : ⟦ Δ ⟧ᶜ
  θ : ⟦ Θ ⟧ᶜ

--------------------
-- Approximations --
--------------------

data ⟦_⟧[_≲ᵗ_] : ∀ α → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type where
  tt        : ⟦ `Unit ⟧[ tt ≲ᵗ tt ]
  false     : ⟦ `Bool ⟧[ false ≲ᵗ false ]
  true      : ⟦ `Bool ⟧[ true ≲ᵗ true ]
  _,_       : ∀ {v₁ v₁′ v₂ v₂′}
            → ⟦ α ⟧[ v₁ ≲ᵗ v₁′ ]
            → ⟦ β ⟧[ v₂ ≲ᵗ v₂′ ]
            → ⟦ α `× β ⟧[ v₁ , v₂ ≲ᵗ v₁′ , v₂′ ]
  undefined : ∀ {v}
            → ⟦ `T α ⟧[ undefined ≲ᵗ v ]
  thunk     : ∀ {v₁ v₂}
            → ⟦ α ⟧[ v₁ ≲ᵗ v₂ ]
            → ⟦ `T α ⟧[ thunk v₁ ≲ᵗ thunk v₂ ]
  []        : ⟦ `ListA α ⟧[ [] ≲ᵗ [] ]
  _∷_       : ∀ {v₁ vs₁ v₂ vs₂}
            → ⟦ α ⟧[ v₁ ≲ᵗ v₂ ]
            → ⟦ `T (`ListA α) ⟧[ vs₁ ≲ᵗ vs₂ ]
            → ⟦ `ListA α ⟧[ v₁ ∷ vs₁ ≲ᵗ v₂ ∷ vs₂ ]

_≲ᵗ_ : ∀ {α} → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type
_≲ᵗ_ = ⟦ _ ⟧[_≲ᵗ_]

⟦_⟧[_≴ᵗ_] : ∀ α → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type
⟦ α ⟧[ v₁ ≴ᵗ v₂ ] = ¬ ⟦ α ⟧[ v₁ ≲ᵗ v₂ ]

⟦_⟧[_≲ᶜ_] : ∀ Γ → ⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ → Type
⟦ Γ ⟧[ γ₁ ≲ᶜ γ₂ ] = AllPointwise _≲ᵗ_ γ₁ γ₂

_≲ᶜ_ : ∀ {Γ} → ⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ → Type
_≲ᶜ_ = ⟦ _ ⟧[_≲ᶜ_]

-----------
-- Terms --
-----------

infix 1 _⊢_
data _⊢_ : Ctx → Ty → Type where

  `_               : α ∈ᴸ Γ → Γ ⊢ α

  `let_`in_        : Γ ⊢ α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β

  `tt              : Γ ⊢ `Unit

  `false           : Γ ⊢ `Bool
  `true            : Γ ⊢ `Bool

  `if_`then_`else_ : Γ ⊢ `Bool
                   → Γ ⊢ α
                   → Γ ⊢ α
                   → Γ ⊢ α

  _`≟_             : Γ ⊢ α
                   → Γ ⊢ α
                   → Γ ⊢ `Bool

  _`≲_             : Γ ⊢ α
                   → Γ ⊢ α
                   → Γ ⊢ `Bool

  _`,_             : Γ ⊢ α
                   → Γ ⊢ β
                   → Γ ⊢ α `× β

  `proj₁           : Γ ⊢ α `× β
                   → Γ ⊢ α

  `proj₂           : Γ ⊢ α `× β
                   → Γ ⊢ β

  `undefined       : Γ ⊢ `T α

  `thunk           : Γ ⊢ α
                   → Γ ⊢ `T α

  `T-case          : Γ ⊢ `T α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ β

  #_               : ℕ → Γ ⊢ `ℕ

  _`+_             : Γ ⊢ `ℕ
                   → Γ ⊢ `ℕ
                   → Γ ⊢ `ℕ

  `[]              : Γ ⊢ `ListA α

  _`∷_             : Γ ⊢ α
                   → Γ ⊢ `T (`ListA α)
                   → Γ ⊢ `ListA α

  `foldrA          : Γ ⸴ α ⸴ `T β ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ `ListA α
                   → Γ ⊢ β

  `free            : Γ ⊢ α

  _`?_             : Γ ⊢ α
                   → Γ ⊢ α
                   → Γ ⊢ α

  `fail            : Γ ⊢ α

variable
  t t₁ t₂ t₃ : Γ ⊢ α

instance

  Number-ℕ : Number ℕ
  Number-ℕ = record
    { Constraint = const ⊤
    ; fromNat    = λ n → n
    }

  Number-Tm : ∀ {Γ} → Number (Γ ⊢ `ℕ)
  Number-Tm = record
    { Constraint = const ⊤
    ; fromNat    = λ n → # n
    }

----------------
-- Evaluation --
----------------

mutual

  data ⟦_⟧ᵉ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧ᶜ → ⟦ α ⟧ᵗ → Type where
    ⇓_                : (x : α ∈ᴸ Γ) → ⟦ ` x ⟧ᵉ γ (All.lookup γ x)
    ⇓let_⇓in_         : ∀ {v₁ v₂} →
      ⟦ t₁ ⟧ᵉ γ ∋ v₁ →
      ⟦ t₂ ⟧ᵉ (γ ⸴ v₁) ∋ v₂ →
      ⟦ `let t₁ `in t₂ ⟧ᵉ γ ∋ v₂
    ⇓tt               : ⟦ `tt ⟧ᵉ γ ∋ tt
    ⇓false            : ⟦ `false ⟧ᵉ γ ∋ false
    ⇓true             : ⟦ `true ⟧ᵉ γ ∋ true
    ⇓if_⇓else_ : ∀ {v} →
      ⟦ t₁ ⟧ᵉ γ ∋ false →
      ⟦ t₃ ⟧ᵉ γ ∋ v →
      ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ ∋ v
    ⇓if_⇓then_ : ∀ {v} →
      ⟦ t₁ ⟧ᵉ γ ∋ true →
      ⟦ t₂ ⟧ᵉ γ ∋ v →
      ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ ∋ v
    ⇓≟-true : {v : ⟦ α ⟧ᵗ} →
      ⟦ t₁ ⟧ᵉ γ ∋ v →
      ⟦ t₂ ⟧ᵉ γ ∋ v →
      ⟦ t₁ `≟ t₂ ⟧ᵉ γ ∋ true
    ⇓≟-false : {v₁ v₂ : ⟦ α ⟧ᵗ}
             → ⟦ t₁ ⟧ᵉ γ ∋ v₁
             → ⟦ t₂ ⟧ᵉ γ ∋ v₂
             → v₁ ≢ v₂
             → ⟦ t₁ `≟ t₂ ⟧ᵉ γ ∋ false
    ⇓≲-true : {v₁ v₂ : ⟦ α ⟧ᵗ} →
      ⟦ t₁ ⟧ᵉ γ ∋ v₁ →
      ⟦ t₂ ⟧ᵉ γ ∋ v₂ →
      ⟦ α ⟧[ v₁ ≲ᵗ v₂ ] →
      ⟦ t₁ `≲ t₂ ⟧ᵉ γ ∋ true
    ⇓≲-false : {v₁ v₂ : ⟦ α ⟧ᵗ}
             → ⟦ t₁ ⟧ᵉ γ ∋ v₁
             → ⟦ t₂ ⟧ᵉ γ ∋ v₂
             → ⟦ α ⟧[ v₁ ≴ᵗ v₂ ]
             → ⟦ t₁ `≲ t₂ ⟧ᵉ γ ∋ false
    _⇓,_ : ∀ {v₁ v₂} →
      ⟦ t₁ ⟧ᵉ γ ∋ v₁ →
      ⟦ t₂ ⟧ᵉ γ ∋ v₂ →
      ⟦ t₁ `, t₂ ⟧ᵉ γ ∋ (v₁ , v₂)
    ⇓proj₁ : ∀ {v} →
      ⟦ t ⟧ᵉ γ ∋ v →
      ⟦ `proj₁ t ⟧ᵉ γ ∋ proj₁ v
    ⇓proj₂ : ∀ {v}
      → ⟦ t ⟧ᵉ γ v
      → ⟦ `proj₂ t ⟧ᵉ γ ∋ proj₂ v
    ⇓undefined : ⟦ `undefined {α = α} ⟧ᵉ γ ∋ undefined
    ⇓thunk : ∀ {v} →
      ⟦ t₁ ⟧ᵉ γ ∋ v →
      ⟦ `thunk t₁ ⟧ᵉ γ ∋ thunk v
    ⇓T-case-undefined : ∀ {v} →
      ⟦ t₁ ⟧ᵉ γ ∋ undefined →
      ⟦ t₃ ⟧ᵉ γ ∋ v →
      ⟦ `T-case t₁ t₂ t₃ ⟧ᵉ γ ∋ v
    ⇓T-case-thunk     : ∀ {v₁ v₂} →
      ⟦ t₁ ⟧ᵉ γ ∋ thunk v₁ →
      ⟦ t₂ ⟧ᵉ (γ ⸴ v₁) ∋ v₂ →
      ⟦ `T-case t₁ t₂ t₃ ⟧ᵉ γ ∋ v₂
    ⇓#_               : ∀ n → ⟦ # n ⟧ᵉ γ n
    _⇓+_              : ∀ {n₁ n₂} →
      ⟦ t₁ ⟧ᵉ γ ∋ n₁ →
      ⟦ t₂ ⟧ᵉ γ ∋ n₂ →
      ⟦ t₁ `+ t₂ ⟧ᵉ γ ∋ (n₁ + n₂)
    ⇓[]               : ∀ {α} → ⟦_⟧ᵉ {α = `ListA α} `[] γ []
    _⇓∷_              : ∀ {x xs} → ⟦ t₁ ⟧ᵉ γ x → ⟦ t₂ ⟧ᵉ γ xs → ⟦ t₁ `∷ t₂ ⟧ᵉ γ (x ∷ xs)
    ⇓foldrA           : ∀ {xs v}
                      → ⟦ t₃ ⟧ᵉ γ xs
                      → ⟦foldrA t₁ , t₂ ⟧ᵉ γ xs ∋ v
                      → ⟦ `foldrA t₁ t₂ t₃ ⟧ᵉ γ v
    ⇓free             : (v : ⟦ α ⟧ᵗ) → ⟦ `free ⟧ᵉ γ v
    ⇓?ˡ               : ∀ {x} → ⟦ t₁ ⟧ᵉ γ x → ⟦ t₁ `? t₂ ⟧ᵉ γ x
    ⇓?ʳ               : ∀ {x} → ⟦ t₂ ⟧ᵉ γ x → ⟦ t₁ `? t₂ ⟧ᵉ γ x

  data ⟦foldrA_,_⟧ᵉ (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                    (t₂ : Γ ⊢ β)
                    (γ : ⟦ Γ ⟧ᶜ) :
                    ListA ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ → Type where
    ⇓foldrA-[] : ∀ {b}
               → ⟦ t₂ ⟧ᵉ γ ∋ b
               → ⟦foldrA t₁ , t₂ ⟧ᵉ γ [] ∋ b
    ⇓foldrA-∷ : ∀ {a asT b₁ b₂}
              → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ asT ∋ b₁
              → ⟦ t₁ ⟧ᵉ (γ ⸴ a ⸴ b₁) ∋ b₂
              → ⟦foldrA t₁ , t₂ ⟧ᵉ γ (a ∷ asT) ∋ b₂

  data ⟦foldrA′_,_⟧ᵉ (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                     (t₂ : Γ ⊢ β)
                     (γ : ⟦ Γ ⟧ᶜ) :
                     T (ListA ⟦ α ⟧ᵗ) → T ⟦ β ⟧ᵗ → Type where
    ⇓foldrA-undefined : ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ undefined ∋ undefined
    ⇓foldrA-thunk     : ∀ {as b}
                      → ⟦foldrA t₁ , t₂ ⟧ᵉ γ as ∋ b
                      → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ (thunk as) ∋ thunk b

---------------------------
-- Some evaluation theorems
---------------------------

-- A special case of subsitution for evaluation
⇓≡ : ∀ {v₁ v₂} → v₁ ≡ v₂ → ⟦ t ⟧ᵉ γ ∋ v₁ → ⟦ t ⟧ᵉ γ ∋ v₂
⇓≡ refl φ = φ

-- Sometimes, trying to pattern match on the evaluation rule for variables
-- causes unification failures.  This can get around that problem.
⇑ : ∀ {x : α ∈ᴸ Γ} {v} → ⟦ ` x ⟧ᵉ γ ∋ v → All.lookup γ x ≡ v
⇑ (⇓ x) = refl
