module LogicalLaziness.Language.Logic where

open import Agda.Builtin.FromNat

open import Effect.Monad.Writer
open import Function
  hiding (_∋_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.TypeClasses
open import Relation.Binary.PropositionalEquality

open import Data.Unit
  using (⊤)
open import Data.Bool
  as Bool
  using (Bool; false; true)
open import Data.Bool.Instances
open import Data.Product
  as Σ
open import Data.Product.Properties
  as Σ
open import Data.Sum
open import Data.Nat
  as ℕ
  using (ℕ; suc; _+_)
open import Data.Nat.Properties
open import Data.List
  as List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
  as All
open import Data.List.Relation.Unary.All.Properties
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Effect.Monad.Tick
import LogicalLaziness.Base.Data.List.All as All
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Base.Data.T
  as T
  hiding (All)
open import LogicalLaziness.Base.Data.ListA
  as ListA
open import LogicalLaziness.Language.Explicit
  as Explicit
  hiding ( Ty
         ; Ctx
         ; _⊢_
         ; `_
         ; `let_`in_
         ; `false
         ; `true
         ; `if_`then_`else_
         ; `[]
         ; _`∷_
         ; `foldr
         ; `tick
         ; `lazy
         ; `force
         )
import LogicalLaziness.Language.Explicit.Semantics.Eval
  as 𝔼
import LogicalLaziness.Language.Explicit.Semantics.Clairvoyant
  as ℂ
open import LogicalLaziness.Language.Explicit.Semantics.Demand
  as 𝔻
  using ( false
        ; true
        ; undefined
        ; thunk
        ; []
        ; _∷_
        )

infixr 5 _`×_
data Ty : Type where
  `Bool  : Ty
  _`×_   : Ty → Ty → Ty
  `T     : Ty → Ty
  `ℕ     : Ty
  `ListA : Ty → Ty

variable
  α α₁ α₂ β τ τ₁ τ₂ τ₃ : Ty

Ctx : Type
Ctx = List Ty

variable
  Γ Γ₁ Γ₂ Δ : Ctx

infix  1.59  `_ ⇓_ #_
infixl 1.56  _`+_ _⇓+_
infixr 1.55  _`∷_ _⇓∷_
infixr 1.54  _`,_ _⇓,_
infix  1.54  _`≟_ _`≲_
infixr 1.51  _`?_ _`>>=_ _⇓>>=_
infix  1.505 `if_`then_`else_ `assert_`in_ ⇓assert_⇓in_ ⇓if_⇓then_ ⇓if_⇓else_
infix  1.50  `let_`in_ ⇓let_⇓in_

infix 2 _⊢_
data _⊢_ : Ctx → Ty → Type where

  `_               : τ ∈ᴸ Γ → Γ ⊢ τ

  `let_`in_        : Γ ⊢ α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β

  `false           : Γ ⊢ `Bool
  `true            : Γ ⊢ `Bool

  `if_`then_`else_ : Γ ⊢ `Bool
                   → Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ τ

  _`≟_             : Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ `Bool

  _`≲_             : Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ `Bool

  _`,_             : Γ ⊢ α
                   → Γ ⊢ β
                   → Γ ⊢ α `× β

  `proj₁             : Γ ⊢ α `× β
                   → Γ ⊢ α

  `proj₂             : Γ ⊢ α `× β
                   → Γ ⊢ β

  `undefined       : Γ ⊢ `T τ

  `thunk           : Γ ⊢ τ
                   → Γ ⊢ `T τ

  `T-case          : Γ ⊢ `T α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ β

  #_               : ℕ → Γ ⊢ `ℕ

  _`+_             : Γ ⊢ `ℕ
                   → Γ ⊢ `ℕ
                   → Γ ⊢ `ℕ

  `[]              : Γ ⊢ `ListA τ

  _`∷_             : Γ ⊢ τ
                   → Γ ⊢ `T (`ListA τ)
                   → Γ ⊢ `ListA τ

  `foldrA          : Γ ⸴ α ⸴ `T β ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ `ListA α
                   → Γ ⊢ β

  `free            : Γ ⊢ τ

  _`?_             : Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ τ

  `fail            : Γ ⊢ τ

variable
  t t′ t₁ t₂ t₃ : Γ ⊢ τ

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

⟦_⟧ᵗ : Ty → Type
⟦ `Bool    ⟧ᵗ = Bool
⟦ α `× β   ⟧ᵗ = ⟦ α ⟧ᵗ × ⟦ β ⟧ᵗ
⟦ `T α     ⟧ᵗ = T ⟦ α ⟧ᵗ
⟦ `ℕ       ⟧ᵗ = ℕ
⟦ `ListA α ⟧ᵗ = ListA ⟦ α ⟧ᵗ

⟦_⟧ᶜ : Ctx → Type
⟦_⟧ᶜ = All ⟦_⟧ᵗ

variable
  γ  : ⟦ Γ ⟧ᶜ
  γ₁ : ⟦ Γ₁ ⟧ᶜ
  γ₂ : ⟦ Γ₂ ⟧ᶜ
  δ  : ⟦ Δ ⟧ᶜ

---------------
-- Renamings --
---------------

infix 2 _→ʳ_
_→ʳ_ : Ctx → Ctx → Type
Γ →ʳ Δ = ∀ {α} → α ∈ᴸ Γ → α ∈ᴸ Δ

variable
  ρ ρ₁ ρ₂ : Γ →ʳ Δ

↑ʳ_ : Γ →ʳ Δ → Γ ⸴ τ →ʳ Δ ⸴ τ
↑ʳ_ ρ zeroᵛ    = zeroᵛ
↑ʳ_ ρ (sucᵛ x) = sucᵛ (ρ x)

infixr -1 _$ʳ_
_$ʳ_ : Γ →ʳ Δ → Γ ⊢ α → Δ ⊢ α
ρ $ʳ ` x                      = ` ρ x
ρ $ʳ `let t₁ `in t₂           = `let (ρ $ʳ t₁) `in (↑ʳ ρ $ʳ t₂)
ρ $ʳ `false                   = `false
ρ $ʳ `true                    = `true
ρ $ʳ `if t₁ `then t₂ `else t₃ = `if (ρ $ʳ t₁) `then ρ $ʳ t₂ `else (ρ $ʳ t₃)
ρ $ʳ t₁ `≟ t₂                 = (ρ $ʳ t₁) `≟ (ρ $ʳ t₂)
ρ $ʳ t₁ `≲ t₂                 = (ρ $ʳ t₁) `≲ (ρ $ʳ t₂)
ρ $ʳ t₁ `, t₂                 = (ρ $ʳ t₁) `, (ρ $ʳ t₂)
ρ $ʳ `proj₁ t₁                = `proj₁ (ρ $ʳ t₁)
ρ $ʳ `proj₂ t₁                = `proj₂ (ρ $ʳ t₁)
ρ $ʳ `undefined               = `undefined
ρ $ʳ `thunk t₁                = `thunk (ρ $ʳ t₁)
ρ $ʳ `T-case t₁ t₂ t₃         = `T-case (ρ $ʳ t₁) (↑ʳ ρ $ʳ t₂) (ρ $ʳ t₃)
ρ $ʳ # x                      = # x
ρ $ʳ t₁ `+ t₂                 = (ρ $ʳ t₁) `+ (ρ $ʳ t₂)
ρ $ʳ `[]                      = `[]
ρ $ʳ t₁ `∷ t₂                 = (ρ $ʳ t₁) `∷ (ρ $ʳ t₂)
ρ $ʳ `foldrA t₁ t₂ t₃         = `foldrA (↑ʳ ↑ʳ ρ $ʳ t₁) (ρ $ʳ t₂) (ρ $ʳ t₃)
ρ $ʳ `free                    = `free
ρ $ʳ t₁ `? t₂                 = (ρ $ʳ t₁) `? (ρ $ʳ t₂)
ρ $ʳ `fail                    = `fail

↑ᵗ_ : Γ ⊢ α
    → Γ ⸴ τ ⊢ α
↑ᵗ_ = (sucᵛ $ʳ_)

exchange : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
exchange t = rename-exchange $ʳ t
  where
    rename-exchange : α ∈ᴸ Γ ⸴ τ₁ ⸴ τ₂ → α ∈ᴸ Γ ⸴ τ₂ ⸴ τ₁
    rename-exchange (here px)        = sucᵛ (here px)
    rename-exchange (sucᵛ (here px)) = here px
    rename-exchange (sucᵛ (sucᵛ p))  = sucᵛ (sucᵛ p)

-- A common special-case context manipulation
subsume1 : Γ ⸴ τ₁ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
subsume1 t = exchange (↑ᵗ t)

-- An uncommon special-case context manipulation
subsume2 : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α → Γ ⸴ τ₃ ⸴ τ₁ ⸴ τ₂ ⊢ α
subsume2 t = rename-subsume2 $ʳ t
  where
    rename-subsume2 : α ∈ᴸ Γ ⸴ τ₁ ⸴ τ₂ → α ∈ᴸ Γ ⸴ τ₃ ⸴ τ₁ ⸴ τ₂
    rename-subsume2 (here px) = here px
    rename-subsume2 (sucᵛ (here px)) = there (here px)
    rename-subsume2 (sucᵛ (sucᵛ x)) = there (there (there x))

-------------------
-- Substitutions --
-------------------

-- A substitution on contexts Γ →ˢ Δ is a mapping that shows, for each α ∈ Γ,
-- how to prove Δ ⊢ α.

infix 4 _→ˢ_
_→ˢ_ : Ctx → Ctx → Type
_→ˢ_ Γ Δ = ∀ {α} → α ∈ᴸ Γ → Δ ⊢ α

↑ˢ_ : Γ →ˢ Δ → Γ ⸴ τ →ˢ Δ ⸴ τ
(↑ˢ σ) zeroᵛ     = ` zeroᵛ
(↑ˢ σ) (sucᵛ x) = ↑ᵗ σ x

infixr -1 _$ˢ_
_$ˢ_ : Γ →ˢ Δ → Γ ⊢ τ → Δ ⊢ τ
σ $ˢ ` x                      = σ x
σ $ˢ `let t₁ `in t₂           = `let (σ $ˢ t₁) `in (↑ˢ σ $ˢ t₂)
σ $ˢ `false                   = `false
σ $ˢ `true                    = `true
σ $ˢ `if t₁ `then t₂ `else t₃ = `if (σ $ˢ t₁) `then (σ $ˢ t₂) `else (σ $ˢ t₃)
σ $ˢ t₁ `≟ t₂                 = (σ $ˢ t₁) `≟ (σ $ˢ t₂)
σ $ˢ t₁ `≲ t₂                 = (σ $ˢ t₁) `≲ (σ $ˢ t₂)
σ $ˢ t₁ `, t₂                 = (σ $ˢ t₁) `, (σ $ˢ t₂)
σ $ˢ `proj₁ t₁                = `proj₁ (σ $ˢ t₁)
σ $ˢ `proj₂ t₁                = `proj₂ (σ $ˢ t₁)
σ $ˢ `undefined               = `undefined
σ $ˢ `thunk t₁                = `thunk (σ $ˢ t₁)
σ $ˢ `T-case t₁ t₂ t₃         = `T-case (σ $ˢ t₁) (↑ˢ σ $ˢ t₂) (σ $ˢ t₃)
σ $ˢ (# n)                    = # n
σ $ˢ t₁ `+ t₂                 = (σ $ˢ t₁) `+ (σ $ˢ t₂)
σ $ˢ `[]                      = `[]
σ $ˢ t₁ `∷ t₂                 = (σ $ˢ t₁) `∷ (σ $ˢ t₂)
σ $ˢ `foldrA t₁ t₂ t₃         = `foldrA (↑ˢ ↑ˢ σ $ˢ t₁) (σ $ˢ t₂) (σ $ˢ t₃)
σ $ˢ `free                    = `free
σ $ˢ t₁ `? t₂                 = (σ $ˢ t₁) `? (σ $ˢ t₂)
σ $ˢ `fail                    = `fail

--------------------
-- Approximations --
--------------------

data Ty⟦_⟧[_≲_] : ∀ α → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type where
  false : Ty⟦ `Bool ⟧[ false ≲ false ]
  true : Ty⟦ `Bool ⟧[ true ≲ true ]
  undefined : ∀ {v} → Ty⟦ `T α ⟧[ undefined ≲ v ]
  thunk : ∀ {v₁ v₂} → Ty⟦ α ⟧[ v₁ ≲ v₂ ] → Ty⟦ `T α ⟧[ thunk v₁ ≲ thunk v₂ ]
  [] : Ty⟦ `ListA α ⟧[ [] ≲ [] ]
  _∷_ : ∀ {v₁ vs₁ v₂ vs₂} → Ty⟦ α ⟧[ v₁ ≲ v₂ ] → Ty⟦ `T (`ListA α) ⟧[ vs₁ ≲ vs₂ ] →
    Ty⟦ `ListA α ⟧[ v₁ ∷ vs₁ ≲ v₂ ∷ vs₂ ]

Ty⟦_⟧[_≴_] : ∀ α → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type
Ty⟦ α ⟧[ v₁ ≴ v₂ ] = ¬ Ty⟦ α ⟧[ v₁ ≲ v₂ ]

----------------
-- Evaluation --
----------------

mutual

  data ⟦_⟧ᵉ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ᶜ → ⟦ τ ⟧ᵗ → Type where
    ⇓_                : (x : τ ∈ᴸ Γ) → ⟦ ` x ⟧ᵉ γ (All.lookup γ x)
    ⇓let_⇓in_         : ∀ {v₁ v₂} →
      ⟦ t₁ ⟧ᵉ γ ∋ v₁ →
      ⟦ t₂ ⟧ᵉ (γ ⸴ v₁) ∋ v₂ →
      ⟦ `let t₁ `in t₂ ⟧ᵉ γ ∋ v₂
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
    ⇓≟-true : {v : ⟦ τ ⟧ᵗ} →
      ⟦ t₁ ⟧ᵉ γ ∋ v →
      ⟦ t₂ ⟧ᵉ γ ∋ v →
      ⟦ t₁ `≟ t₂ ⟧ᵉ γ ∋ true
    ⇓≟-false : {v₁ v₂ : ⟦ τ ⟧ᵗ}
             → ⟦ t₁ ⟧ᵉ γ ∋ v₁
             → ⟦ t₂ ⟧ᵉ γ ∋ v₂
             → v₁ ≢ v₂
             → ⟦ t₁ `≟ t₂ ⟧ᵉ γ ∋ false
    ⇓≲-true : {v₁ v₂ : ⟦ τ ⟧ᵗ} →
      ⟦ t₁ ⟧ᵉ γ ∋ v₁ →
      ⟦ t₂ ⟧ᵉ γ ∋ v₂ →
      Ty⟦ τ ⟧[ v₁ ≲ v₂ ] →
      ⟦ t₁ `≲ t₂ ⟧ᵉ γ ∋ true
    ⇓≲-false : {v₁ v₂ : ⟦ τ ⟧ᵗ}
             → ⟦ t₁ ⟧ᵉ γ ∋ v₁
             → ⟦ t₂ ⟧ᵉ γ ∋ v₂
             → Ty⟦ τ ⟧[ v₁ ≴ v₂ ]
             → ⟦ t₁ `≲ t₂ ⟧ᵉ γ ∋ false
    _⇓,_              : ∀ {v₁ v₂} →
      ⟦ t₁ ⟧ᵉ γ ∋ v₁ →
      ⟦ t₂ ⟧ᵉ γ ∋ v₂ →
      ⟦ t₁ `, t₂ ⟧ᵉ γ ∋ (v₁ , v₂)
    ⇓proj₁ : ∀ {v} →
      ⟦ t ⟧ᵉ γ ∋ v →
      ⟦ `proj₁ t ⟧ᵉ γ ∋ proj₁ v
    ⇓proj₂ : ∀ {v}
      → ⟦ t ⟧ᵉ γ v
      → ⟦ `proj₂ t ⟧ᵉ γ ∋ proj₂ v
    ⇓undefined : ⟦ `undefined {τ = τ} ⟧ᵉ γ ∋ undefined
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
    #_                : ∀ n → ⟦ # n ⟧ᵉ γ n
    _⇓+_              : ∀ {n₁ n₂} →
      ⟦ t₁ ⟧ᵉ γ ∋ n₁ →
      ⟦ t₂ ⟧ᵉ γ ∋ n₂ →
      ⟦ t₁ `+ t₂ ⟧ᵉ γ ∋ (n₁ + n₂)
    ⇓[]               : ∀ {τ} → ⟦_⟧ᵉ {τ = `ListA τ} `[] γ []
    _⇓∷_              : ∀ {x xs} → ⟦ t₁ ⟧ᵉ γ x → ⟦ t₂ ⟧ᵉ γ xs → ⟦ t₁ `∷ t₂ ⟧ᵉ γ (x ∷ xs)
    ⇓foldrA           : ∀ {xs v}
                      → ⟦ t₃ ⟧ᵉ γ xs
                      → ⟦foldrA t₁ , t₂ ⟧ᵉ γ xs ∋ v
                      → ⟦ `foldrA t₁ t₂ t₃ ⟧ᵉ γ v
    ⇓free             : ∀ {v : ⟦ α ⟧ᵗ} → ⟦ `free ⟧ᵉ γ v
    ?l                : ∀ {x} → ⟦ t₁ ⟧ᵉ γ x → ⟦ t₁ `? t₂ ⟧ᵉ γ x
    ?r                : ∀ {x} → ⟦ t₂ ⟧ᵉ γ x → ⟦ t₁ `? t₂ ⟧ᵉ γ x

  data ⟦foldrA_,_⟧ᵉ (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                    (t₂ : Γ ⊢ β)
                    (γ : ⟦ Γ ⟧ᶜ) :
                    ListA ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ → Type where
    ⇓foldrA-[] : ∀ {v}
               → ⟦ t₂ ⟧ᵉ γ ∋ v
               → ⟦foldrA t₁ , t₂ ⟧ᵉ γ [] ∋ v
    ⇓foldrA-∷ : ∀ {xT xsT v v′}
              → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ xsT ∋ v
              → ⟦ t₁ ⟧ᵉ (γ ⸴ xT ⸴ v) ∋ v′
              → ⟦foldrA t₁ , t₂ ⟧ᵉ γ (xT ∷ xsT) ∋ v′

  data ⟦foldrA′_,_⟧ᵉ (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                     (t₂ : Γ ⊢ β)
                     (γ : ⟦ Γ ⟧ᶜ) :
                     T (ListA ⟦ α ⟧ᵗ) → T ⟦ β ⟧ᵗ → Type where
    ⇓foldrA-undefined : ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ undefined ∋ undefined
    ⇓foldrA-thunk : ∀ {xs v}
                  → ⟦foldrA t₁ , t₂ ⟧ᵉ γ xs ∋ v
                  → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ (thunk xs) ∋ thunk v

--------------------------
-- Some term constructs --
--------------------------

`assert_`in_ : Γ ⊢ `Bool → Γ ⊢ α → Γ ⊢ α
`assert t₁ `in t₂ = `if t₁ `then t₂ `else `fail

⇓assert_⇓in_ : ∀ {v}
             → ⟦ t₁ ⟧ᵉ γ ∋ true
             → ⟦ t₂ ⟧ᵉ γ ∋ v
             → ⟦ `assert t₁ `in t₂ ⟧ᵉ γ ∋ v
⇓assert_⇓in_ φ₁ φ₂ = ⇓if φ₁ ⇓then φ₂

⇑assert : ∀ {v}
        → ⟦ `assert t₁ `in t₂ ⟧ᵉ γ ∋ v
        → ⟦ t₁ ⟧ᵉ γ ∋ true × ⟦ t₂ ⟧ᵉ γ ∋ v
⇑assert (⇓if φ₁ ⇓then φ₂) = φ₁ , φ₂

---------------------------------
-- Context manipulation lemmas --
---------------------------------

↑ʳ-∈ᴸ : (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)
      → ∀ {β} {v : ⟦ β ⟧ᵗ} {α} (x : α ∈ᴸ Γ ⸴ β) → All.lookup (δ ⸴ v) ((↑ʳ ρ) x) ≡ All.lookup (γ ⸴ v) x
↑ʳ-∈ᴸ η zeroᵛ = refl
↑ʳ-∈ᴸ η (sucᵛ x) = η x

mutual

  ⇓⇒$ʳ-⇓ : (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)
         → ∀ {v} {t : Γ ⊢ α}
         → ⟦ t ⟧ᵉ γ ∋ v
         → ⟦ ρ $ʳ t ⟧ᵉ δ ∋ v
  ⇓⇒$ʳ-⇓ {δ = δ} {ρ = ρ} η (⇓ x) = subst (⟦ ` ρ x ⟧ᵉ δ ∋_) (η x) (⇓ ρ x)
  ⇓⇒$ʳ-⇓ η (⇓let φ₁ ⇓in φ₂) = ⇓let ⇓⇒$ʳ-⇓ η φ₁ ⇓in ⇓⇒$ʳ-⇓ (↑ʳ-∈ᴸ η) φ₂
  ⇓⇒$ʳ-⇓ η ⇓false = ⇓false
  ⇓⇒$ʳ-⇓ η ⇓true = ⇓true
  ⇓⇒$ʳ-⇓ η (⇓if φ₁ ⇓else φ₂) = ⇓if ⇓⇒$ʳ-⇓ η φ₁ ⇓else ⇓⇒$ʳ-⇓ η φ₂
  ⇓⇒$ʳ-⇓ η (⇓if φ₁ ⇓then φ₂) = ⇓if ⇓⇒$ʳ-⇓ η φ₁ ⇓then ⇓⇒$ʳ-⇓ η φ₂
  ⇓⇒$ʳ-⇓ η (⇓≟-true φ₁ φ₂) = ⇓≟-true (⇓⇒$ʳ-⇓ η φ₁) (⇓⇒$ʳ-⇓ η φ₂)
  ⇓⇒$ʳ-⇓ η (⇓≟-false φ₁ φ₂ ψ) = ⇓≟-false (⇓⇒$ʳ-⇓ η φ₁) (⇓⇒$ʳ-⇓ η φ₂) ψ
  ⇓⇒$ʳ-⇓ η (⇓≲-true φ₁ φ₂ ψ) = ⇓≲-true (⇓⇒$ʳ-⇓ η φ₁) (⇓⇒$ʳ-⇓ η φ₂) ψ
  ⇓⇒$ʳ-⇓ η (⇓≲-false φ₁ φ₂ ψ) = ⇓≲-false (⇓⇒$ʳ-⇓ η φ₁) (⇓⇒$ʳ-⇓ η φ₂) ψ
  ⇓⇒$ʳ-⇓ η (φ₁ ⇓, φ₂) = ⇓⇒$ʳ-⇓ η φ₁ ⇓, ⇓⇒$ʳ-⇓ η φ₂
  ⇓⇒$ʳ-⇓ η (⇓proj₁ φ) = ⇓proj₁ (⇓⇒$ʳ-⇓ η φ)
  ⇓⇒$ʳ-⇓ η (⇓proj₂ φ) = ⇓proj₂ (⇓⇒$ʳ-⇓ η φ)
  ⇓⇒$ʳ-⇓ η ⇓undefined = ⇓undefined
  ⇓⇒$ʳ-⇓ η (⇓thunk φ) = ⇓thunk (⇓⇒$ʳ-⇓ η φ)
  ⇓⇒$ʳ-⇓ η (⇓T-case-undefined φ₁ φ₂) = ⇓T-case-undefined (⇓⇒$ʳ-⇓ η φ₁) (⇓⇒$ʳ-⇓ η φ₂)
  ⇓⇒$ʳ-⇓ η (⇓T-case-thunk φ₁ φ₂) = ⇓T-case-thunk (⇓⇒$ʳ-⇓ η φ₁) (⇓⇒$ʳ-⇓ (↑ʳ-∈ᴸ η) φ₂)
  ⇓⇒$ʳ-⇓ η (# n) = # n
  ⇓⇒$ʳ-⇓ η (φ₁ ⇓+ φ₂) = ⇓⇒$ʳ-⇓ η φ₁ ⇓+ ⇓⇒$ʳ-⇓ η φ₂
  ⇓⇒$ʳ-⇓ η ⇓[] = ⇓[]
  ⇓⇒$ʳ-⇓ η (φ₁ ⇓∷ φ₂) = ⇓⇒$ʳ-⇓ η φ₁ ⇓∷ ⇓⇒$ʳ-⇓ η φ₂
  ⇓⇒$ʳ-⇓ η (⇓foldrA φ₁ φ₂) = ⇓foldrA (⇓⇒$ʳ-⇓ η φ₁) (⇓foldrA⇒$ʳ-⇓foldrA η φ₂)
  ⇓⇒$ʳ-⇓ η ⇓free = ⇓free
  ⇓⇒$ʳ-⇓ η (?l φ) = ?l (⇓⇒$ʳ-⇓ η φ)
  ⇓⇒$ʳ-⇓ η (?r φ) = ?r (⇓⇒$ʳ-⇓ η φ)

  ⇓foldrA⇒$ʳ-⇓foldrA : (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)
                     → ∀ {v xs}
                     → ⟦foldrA t₁ , t₂ ⟧ᵉ γ xs ∋ v
                     → ⟦foldrA (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ xs ∋ v
  ⇓foldrA⇒$ʳ-⇓foldrA η (⇓foldrA-[] φ)    = ⇓foldrA-[] (⇓⇒$ʳ-⇓ η φ)
  ⇓foldrA⇒$ʳ-⇓foldrA η (⇓foldrA-∷ φ₁ φ₂) =
    ⇓foldrA-∷
      (⇓foldrA⇒$ʳ-⇓foldrA′ η φ₁)
      (⇓⇒$ʳ-⇓ (λ{ zeroᵛ → refl ; (sucᵛ zeroᵛ) → refl ; (sucᵛ (sucᵛ zeroᵛ)) → η zeroᵛ ; (sucᵛ (sucᵛ (sucᵛ x))) → η (sucᵛ x) }) φ₂)

  ⇓foldrA⇒$ʳ-⇓foldrA′ : (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)
                      → ∀ {v xsT}
                      → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ xsT ∋ v
                      → ⟦foldrA′ (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ xsT ∋ v
  ⇓foldrA⇒$ʳ-⇓foldrA′ η ⇓foldrA-undefined = ⇓foldrA-undefined
  ⇓foldrA⇒$ʳ-⇓foldrA′ η (⇓foldrA-thunk φ) = ⇓foldrA-thunk (⇓foldrA⇒$ʳ-⇓foldrA η φ)

mutual

  $ʳ-⇓⇒⇓ : (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)
         → ∀ {v} {t : Γ ⊢ α}
         → ⟦ ρ $ʳ t ⟧ᵉ δ ∋ v
         → ⟦ t ⟧ᵉ γ ∋ v
  $ʳ-⇓⇒⇓ {δ = δ} {ρ = ρ} {γ = γ} η {t = ` x} (⇓ _) = subst (⟦ ` x ⟧ᵉ γ ∋_) (sym (η x)) (⇓ x)
  $ʳ-⇓⇒⇓ η {t = `let t₁ `in t₂} (⇓let φ₁ ⇓in φ₂) = ⇓let ($ʳ-⇓⇒⇓ η φ₁) ⇓in ($ʳ-⇓⇒⇓ (↑ʳ-∈ᴸ η) φ₂)
  $ʳ-⇓⇒⇓ η {t = `false} ⇓false = ⇓false
  $ʳ-⇓⇒⇓ η {t = `true} ⇓true = ⇓true
  $ʳ-⇓⇒⇓ η {t = `if t₁ `then t₂ `else t₃} (⇓if φ₁ ⇓else φ₂) = ⇓if $ʳ-⇓⇒⇓ η φ₁ ⇓else $ʳ-⇓⇒⇓ η φ₂
  $ʳ-⇓⇒⇓ η {t = `if t₁ `then t₂ `else t₃} (⇓if φ₁ ⇓then φ₂) = ⇓if $ʳ-⇓⇒⇓ η φ₁ ⇓then $ʳ-⇓⇒⇓ η φ₂
  $ʳ-⇓⇒⇓ η {t = t₁ `≟ t₂} (⇓≟-true φ₁ φ₂) = ⇓≟-true ($ʳ-⇓⇒⇓ η φ₁) ($ʳ-⇓⇒⇓ η φ₂)
  $ʳ-⇓⇒⇓ η {t = t₁ `≟ t₂} (⇓≟-false φ₁ φ₂ ψ) = ⇓≟-false ($ʳ-⇓⇒⇓ η φ₁) ($ʳ-⇓⇒⇓ η φ₂) ψ
  $ʳ-⇓⇒⇓ η {t = t₁ `≲ t₂} (⇓≲-true φ₁ φ₂ ψ) = ⇓≲-true ($ʳ-⇓⇒⇓ η φ₁) ($ʳ-⇓⇒⇓ η φ₂) ψ
  $ʳ-⇓⇒⇓ η {t = t₁ `≲ t₂} (⇓≲-false φ₁ φ₂ ψ) = ⇓≲-false ($ʳ-⇓⇒⇓ η φ₁) ($ʳ-⇓⇒⇓ η φ₂) ψ
  $ʳ-⇓⇒⇓ η {t = t₁ `, t₂} (φ₁ ⇓, φ₂) = $ʳ-⇓⇒⇓ η φ₁ ⇓, $ʳ-⇓⇒⇓ η φ₂
  $ʳ-⇓⇒⇓ η {t = `proj₁ t} (⇓proj₁ φ) = ⇓proj₁ ($ʳ-⇓⇒⇓ η φ)
  $ʳ-⇓⇒⇓ η {t = `proj₂ t} (⇓proj₂ φ) = ⇓proj₂ ($ʳ-⇓⇒⇓ η φ)
  $ʳ-⇓⇒⇓ η {t = `undefined} ⇓undefined = ⇓undefined
  $ʳ-⇓⇒⇓ η {t = `thunk t} (⇓thunk φ) = ⇓thunk ($ʳ-⇓⇒⇓ η φ)
  $ʳ-⇓⇒⇓ η {t = `T-case t t₁ t₂} (⇓T-case-undefined φ₁ φ₂) = ⇓T-case-undefined ($ʳ-⇓⇒⇓ η φ₁) ($ʳ-⇓⇒⇓ η φ₂)
  $ʳ-⇓⇒⇓ η {t = `T-case t t₁ t₂} (⇓T-case-thunk φ₁ φ₂) = ⇓T-case-thunk ($ʳ-⇓⇒⇓ η φ₁) ($ʳ-⇓⇒⇓ (λ{ zeroᵛ → refl ; (sucᵛ x) → η x }) φ₂)
  $ʳ-⇓⇒⇓ η {t = # x} (# n) = # x
  $ʳ-⇓⇒⇓ η {t = t₁ `+ t₂} (φ₁ ⇓+ φ₂) = $ʳ-⇓⇒⇓ η φ₁ ⇓+ $ʳ-⇓⇒⇓ η φ₂
  $ʳ-⇓⇒⇓ η {t = `[]} ⇓[] = ⇓[]
  $ʳ-⇓⇒⇓ η {t = t₁ `∷ t₂} (φ₁ ⇓∷ φ₂) = $ʳ-⇓⇒⇓ η φ₁ ⇓∷ $ʳ-⇓⇒⇓ η φ₂
  $ʳ-⇓⇒⇓ η {t = `foldrA t₁ t₂ t₃} (⇓foldrA φ₁ φ₂) = ⇓foldrA ($ʳ-⇓⇒⇓ η φ₁) ($ʳ-⇓foldrA⇒⇓foldrA η φ₂)
  $ʳ-⇓⇒⇓ η {t = `free} ⇓free = ⇓free
  $ʳ-⇓⇒⇓ η {t = t₁ `? t₂} (?l φ) = ?l ($ʳ-⇓⇒⇓ η φ)
  $ʳ-⇓⇒⇓ η {t = t₁ `? t₂} (?r φ) = ?r ($ʳ-⇓⇒⇓ η φ)

  $ʳ-⇓foldrA⇒⇓foldrA : (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)
                     → ∀ {v xs}
                     → ⟦foldrA (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ xs ∋ v
                     → ⟦foldrA t₁ , t₂ ⟧ᵉ γ xs ∋ v
  $ʳ-⇓foldrA⇒⇓foldrA η (⇓foldrA-[] φ) = ⇓foldrA-[] ($ʳ-⇓⇒⇓ η φ)
  $ʳ-⇓foldrA⇒⇓foldrA η (⇓foldrA-∷ φ₁ φ₂) =
    ⇓foldrA-∷
      ($ʳ-⇓foldrA⇒⇓foldrA′ η φ₁)
      ($ʳ-⇓⇒⇓ (λ{ zeroᵛ → refl ; (sucᵛ zeroᵛ) → refl ; (sucᵛ (sucᵛ zeroᵛ)) → η zeroᵛ ; (sucᵛ (sucᵛ (sucᵛ x))) → η (sucᵛ x) }) φ₂)

  $ʳ-⇓foldrA⇒⇓foldrA′ : (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)
                      → ∀ {v xsT}
                      → ⟦foldrA′ (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ xsT ∋ v
                      → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ xsT ∋ v
  $ʳ-⇓foldrA⇒⇓foldrA′ η ⇓foldrA-undefined = ⇓foldrA-undefined
  $ʳ-⇓foldrA⇒⇓foldrA′ η (⇓foldrA-thunk φ) = ⇓foldrA-thunk ($ʳ-⇓foldrA⇒⇓foldrA η φ)

⇓weaken :
  ∀ {Γ α τ} {t : Γ ⊢ τ} {γ : ⟦ Γ ⟧ᶜ} {a : ⟦ α ⟧ᵗ} 
    {v : ⟦ τ ⟧ᵗ}
  → ⟦ t ⟧ᵉ γ ∋ v
  → ⟦ ↑ᵗ t ⟧ᵉ (γ ⸴ a) ∋ v
⇓weaken φ = ⇓⇒$ʳ-⇓ (λ _ → refl) φ

⇑weaken :
  ∀ {Γ α τ} {t : Γ ⊢ τ} {γ : ⟦ Γ ⟧ᶜ} {a : ⟦ α ⟧ᵗ}
    {v : ⟦ τ ⟧ᵗ}
  → ⟦ ↑ᵗ t ⟧ᵉ (γ ⸴ a) ∋ v
  → ⟦ t ⟧ᵉ γ ∋ v
⇑weaken φ = $ʳ-⇓⇒⇓ (λ _ → refl) φ

⇓exchange :
  ∀ {a : ⟦ α ⟧ᵗ}
    {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ}
  → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ a
  → ⟦ exchange t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ a
⇓exchange φ = ⇓⇒$ʳ-⇓ (λ{ zeroᵛ → refl ; (sucᵛ zeroᵛ) → refl ; (sucᵛ (sucᵛ x)) → refl }) φ

⇑exchange :
  ∀ {a : ⟦ α ⟧ᵗ}
    {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ}
  → ⟦ exchange t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ a
  → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ a
⇑exchange φ = $ʳ-⇓⇒⇓ (λ{ zeroᵛ → refl ; (sucᵛ zeroᵛ) → refl ; (sucᵛ (sucᵛ x)) → refl }) φ

⇓subsume1 : {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
          → ⟦ t ⟧ᵉ (γ ⸴ v₁) ∋ v
          → ⟦ subsume1 t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ v
⇓subsume1 φ = ⇓exchange (⇓weaken φ)

⇑subsume1 : {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
          → ⟦ subsume1 t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ v
          → ⟦ t ⟧ᵉ (γ ⸴ v₁) ∋ v
⇑subsume1 φ = ⇑weaken (⇑exchange φ)

⇓subsume2 : ∀ {v₁ v₂} {v₃ : ⟦ τ₃ ⟧ᵗ} {v}
          → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ v
          → ⟦ subsume2 t ⟧ᵉ (γ ⸴ v₃ ⸴ v₁ ⸴ v₂) ∋ v
⇓subsume2 = ⇓⇒$ʳ-⇓ λ{ zeroᵛ → refl ; (sucᵛ zeroᵛ) → refl ; (sucᵛ (sucᵛ x)) → refl }

⇑subsume2 : ∀ {v₁ v₂} {v₃ : ⟦ τ₃ ⟧ᵗ} {v}
          → ⟦ subsume2 t ⟧ᵉ (γ ⸴ v₃ ⸴ v₁ ⸴ v₂) ∋ v
          → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ v
⇑subsume2 = $ʳ-⇓⇒⇓ λ{ zeroᵛ → refl ; (sucᵛ zeroᵛ) → refl ; (sucᵛ (sucᵛ x)) → refl }

---------------------------------------------------------
-- A few special cases of substitution for evaluation. --
---------------------------------------------------------

private
  variable
    c c₁ c₂ : ℕ

⇓≡ : ∀ {v₁ v₂} → v₁ ≡ v₂ → ⟦ t ⟧ᵉ γ ∋ v₁ → ⟦ t ⟧ᵉ γ ∋ v₂
⇓≡ refl φ = φ

⇓cost≡ : ∀ {v} → c₁ ≡ c₂ → ⟦ t ⟧ᵉ γ ∋ (v , c₁) → ⟦ t ⟧ᵉ γ ∋ (v , c₂)
⇓cost≡ {t = t} {γ = γ} {v = v} refl φ = φ

-------------------------------
-- Object-language writer monad
-------------------------------

`M : Ty → Ty
`M α = α `× `ℕ

_`>>=_ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → Γ ⊢ `M β
t₁ `>>= t₂ =
  `let t₁ `in
  `let (`let `proj₁ (` zeroᵛ) `in subsume1 t₂) `in
  (`proj₁ (` zeroᵛ) `, (`proj₂ (` (sucᵛ zeroᵛ)) `+ `proj₂ (` zeroᵛ)))

data ⟦>>=_,_⟧ᵉ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → ⟦ Γ ⟧ᶜ → ⟦ β ⟧ᵗ × ℕ → Type where
  ⇓>>=-intro : ∀ {a b c₁ c₂}
               → ⟦ t₁ ⟧ᵉ γ ∋ (a , c₁)
               → ⟦ t₂ ⟧ᵉ (γ ⸴ a) ∋ (b , c₂)
               → ⟦>>= t₁ , t₂ ⟧ᵉ γ ∋ (b , c₁ + c₂)

⇓>>= : ∀ {u} → ⟦>>= t₁ , t₂ ⟧ᵉ γ u → ⟦ t₁ `>>= t₂ ⟧ᵉ γ u
⇓>>= (⇓>>=-intro φ₁ φ₂) =
  ⇓let φ₁ ⇓in
  ⇓let (⇓let ⇓proj₁ (⇓ zeroᵛ) ⇓in ⇓subsume1 φ₂) ⇓in
  ⇓proj₁ (⇓ zeroᵛ) ⇓, ⇓proj₂ (⇓ sucᵛ zeroᵛ) ⇓+ ⇓proj₂ (⇓ zeroᵛ)

⇑>>= : ∀ {u} → ⟦ t₁ `>>= t₂ ⟧ᵉ γ u → ⟦>>= t₁ , t₂ ⟧ᵉ γ u
⇑>>= (⇓let φ₁ ⇓in
      ⇓let (⇓let ⇓proj₁ (⇓ _) ⇓in φ₂) ⇓in
      ⇓proj₁ (⇓ .zeroᵛ) ⇓, (⇓proj₂ (⇓ sucᵛ zeroᵛ) ⇓+ ⇓proj₂ (⇓ zeroᵛ))) =
  ⇓>>=-intro φ₁ (⇑subsume1 φ₂)

`return : Γ ⊢ α → Γ ⊢ `M α
`return t = t `, 0

-- `return is purely structural, so we don't need to prove an inversion lemma
pattern ⇓return φ = φ ⇓, # 0

`tick : Γ ⊢ `M α → Γ ⊢ `M α
`tick t = `let t `in `proj₁ (` zeroᵛ) `, 1 `+ `proj₂ (` zeroᵛ)

pattern ⇓tick φ = ⇓let φ ⇓in ⇓proj₁ (⇓ zeroᵛ) ⇓, # 1 ⇓+ ⇓proj₂ (⇓ zeroᵛ)

-- Is fmap the right name for this?  Is this even the right function?
`fmap : (∀ {Δ} → Δ ⊢ α → Δ ⊢ β) → Γ ⊢ `M α → Γ ⊢ `M β
`fmap f t = `let t `in f (`proj₁ (` zeroᵛ)) `, `proj₂ (` zeroᵛ)

⇓fmap : ∀ (f : ∀ {Δ} → Δ ⊢ α → Δ ⊢ β)
          (g : ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ)
      → (∀ {t δ v} → ⟦ t ⟧ᵉ δ ∋ v → ⟦ f t ⟧ᵉ δ ∋ g v)
      → ∀ {t v c}
      → ⟦ t ⟧ᵉ γ ∋ (v , c)
      → ⟦ `fmap f t ⟧ᵉ γ ∋ (g v , c)
⇓fmap f g η φ = ⇓let φ ⇓in η (⇓proj₁ (⇓ zeroᵛ)) ⇓, ⇓proj₂ (⇓ zeroᵛ)

⇑fmap : ∀ (f : ∀ {Δ} → Δ ⊢ α → Δ ⊢ β)
          (g : ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ)
        → (∀ {Δ} {t : Δ ⊢ α} {δ v} → ⟦ f t ⟧ᵉ δ ∋ g v → ⟦ t ⟧ᵉ δ ∋ v)
        → ∀ {t v c}
        → ⟦ `fmap f t ⟧ᵉ γ ∋ (g v , c)
        → ⟦ t ⟧ᵉ γ ∋ (v , c)
⇑fmap f g η (⇓let φ₁ ⇓in φ₂ ⇓, ⇓proj₂ (⇓ x)) with η φ₂
... | ⇓proj₁ (⇓ _) = φ₁

-- Transpose T and M

`transposeM : Γ ⊢ `T (`M α) → Γ ⊢ `M (`T α)
`transposeM t = `T-case t (` zeroᵛ `>>= `return (`thunk (` zeroᵛ))) (`return `undefined)

data ⟦transposeM_⟧ᵉ : Γ ⊢ `T (`M α) → ⟦ Γ ⟧ᶜ → T ⟦ α ⟧ᵗ × ℕ → Type where
  transposeM-undefined : ⟦ t ⟧ᵉ γ ∋ undefined
                       → ⟦transposeM t ⟧ᵉ γ ∋ (undefined , 0)
  transposeM-thunk : ∀ {v}
                   → ⟦ t ⟧ᵉ γ ∋ thunk (v , c)
                   → ⟦transposeM t ⟧ᵉ γ ∋ (thunk v , c)

⇓transposeM : ∀ {u} → ⟦transposeM t ⟧ᵉ γ ∋ u → ⟦ `transposeM t ⟧ᵉ γ ∋ u
⇓transposeM (transposeM-undefined φ) = ⇓T-case-undefined φ (⇓undefined ⇓, # 0)
⇓transposeM (transposeM-thunk φ)     =
  ⇓T-case-thunk φ (⇓cost≡ (+-identityʳ _) (⇓>>= (⇓>>=-intro (⇓ zeroᵛ) (⇓thunk (⇓ zeroᵛ) ⇓, # 0))))

⇑transposeM : ∀ {u} → ⟦ `transposeM t ⟧ᵉ γ ∋ u → ⟦transposeM t ⟧ᵉ γ ∋ u
⇑transposeM (⇓T-case-undefined φ₁ (⇓return ⇓undefined)) = transposeM-undefined φ₁
⇑transposeM {t = t} {γ = γ} (⇓T-case-thunk φ₁ φ₂) with ⇑>>= φ₂
... | ⇓>>=-intro (⇓ _) (⇓return (⇓thunk (⇓ _))) =
  transposeM-thunk (subst (λ v → ⟦ t ⟧ᵉ γ ∋ thunk v) (×-≡,≡→≡ (refl , sym (+-identityʳ _))) φ₁)

-- ⇓transposeM-undefined : ⟦ t ⟧ᵉ γ ∋ undefined
--                       → ⟦ `transposeM t ⟧ᵉ γ ∋ (undefined , 0)
-- ⇓transposeM-undefined φ = ⇓T-case-undefined φ (⇓undefined ⇓, # 0)

-- ⇓transposeM-thunk : ∀ {v}
--                   → ⟦ t ⟧ᵉ γ ∋ thunk (v , c)
--                   → ⟦ `transposeM t ⟧ᵉ γ ∋ (thunk v , c)
-- ⇓transposeM-thunk φ =
--   ⇓T-case-thunk φ (⇓cost≡ (+-identityʳ _) (⇓>>= (⇓>>=-intro (⇓ zeroᵛ) (⇓thunk (⇓ zeroᵛ) ⇓, # 0))))

-- ⇑transposeM : ∀ {α} {t : Γ ⊢ `T (`M α)} {γ v c}
--             → ⟦ `transposeM t ⟧ᵉ γ ∋ (v , c)
--             → (c ≡ 0 × ⟦ t ⟧ᵉ γ ∋ undefined) ⊎ (Σ[ v′ ∈ ⟦ α ⟧ᵗ ] (v ≡ thunk v′ × ⟦ t ⟧ᵉ γ ∋ thunk (v′ , c)))
-- ⇑transposeM (⇓T-case-undefined φ₁ (⇓return _)) = inj₁ (refl , φ₁)
-- ⇑transposeM {t = t} {γ = γ} (⇓T-case-thunk φ₁ φ₂) with ⇑>>= φ₂
-- ... | (v , c) , c₁ , (⇓ _) , ⇓return (⇓thunk (⇓ _)) , refl =
--   inj₂ (_ , refl , subst (λ v → ⟦ t ⟧ᵉ γ ∋ thunk v) (×-≡,≡→≡ (refl , sym (+-identityʳ _))) φ₁)

-- An additional layer of abstraction that makes foldrM and associated proofs
-- easier

`transposeF : Γ ⸴ α ⸴ `T β ⊢ `M β
            → Γ ⸴ α ⸴ `T (`M β) ⊢ `M β
`transposeF t = `transposeM (` zeroᵛ) `>>= subsume1 t

⇓transposeF-undefined : ∀ {v u} →
                        ⟦ t ⟧ᵉ (γ ⸴ v ⸴ undefined) ∋ u →
                        ⟦ `transposeF t ⟧ᵉ (γ ⸴ v ⸴ undefined) ∋ u
⇓transposeF-undefined φ = {!⇓transposeM-undefined!}
-- ⇓transposeM-undefined ?
-- (⇓>>= (⇓>>=-intro (⇓ zeroᵛ) (⇓subsume1 φ)))

⇓transposeF-thunk : ∀ {v₁ : ⟦ α ⟧ᵗ} {v₂ v₃ c₁ c₂} →
                    ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ thunk v₂) ∋ (v₃ , c₂) →
                    ⟦ `transposeF t ⟧ᵉ (γ ⸴ v₁ ⸴ thunk (v₂ , c₁)) ∋ (v₃ , c₁ + c₂)
⇓transposeF-thunk φ = {!!}
-- ⇓transposeM-thunk (⇓ zeroᵛ) ⇓>>= ⇓subsume1 φ

-- Monadic foldr

`foldrM : Γ ⸴ α ⸴ `T β ⊢ `M β
        → Γ ⊢ `M β
        → Γ ⊢ `ListA α
        → Γ ⊢ `M β
`foldrM t₁ t₂ t₃ = `foldrA (`transposeF t₁) t₂ t₃

-- This relation completely characterizes the reduction behavior of foldrM
-- (needs to be proven)

data ⟦foldrM_,_⟧ᵉ : Γ ⸴ α ⸴ `T β ⊢ `M β
                  → Γ ⊢ `M β
                  → ⟦ Γ ⟧ᶜ
                  → ListA ⟦ α ⟧ᵗ
                  → ⟦ `M β ⟧ᵗ
                  → Type where
  foldrM-[] : ∀ {u} →
              ⟦ t₂ ⟧ᵉ γ ∋ u →
              ---------------------------
              ⟦foldrM t₁ , t₂ ⟧ᵉ γ [] ∋ u

  foldrM-undefined : ∀ {a u} →
                     ⟦ t₁ ⟧ᵉ (γ ⸴ a ⸴ undefined) ∋ u →
                     ----------------------------------------
                     ⟦foldrM t₁ , t₂ ⟧ᵉ γ (a ∷ undefined) ∋ u

  foldrM-thunk : ∀ {v₁} {v₂ : ListA ⟦ β ⟧ᵗ} {v₃ v₄ c₁ c₂} →
                 ⟦foldrM t₁ , t₂ ⟧ᵉ γ v₂ ∋ (v₃ , c₁) →
                 ⟦ t₁ ⟧ᵉ (γ ⸴ v₁ ⸴ thunk v₃) ∋ (v₄ , c₂) →
                 -----------------------------------------------------
                 ⟦foldrM t₁ , t₂ ⟧ᵉ γ (v₁ ∷ thunk v₂) ∋ (v₄ , c₁ + c₂)

⇓foldrM⇒⇓foldrA : ∀ {v u} →
                  ⟦foldrM t₁ , t₂ ⟧ᵉ γ v ∋ u →
                  ⟦foldrA (`transposeF t₁) , t₂ ⟧ᵉ γ v ∋ u
⇓foldrM⇒⇓foldrA (foldrM-[] φ) = ⇓foldrA-[] φ
⇓foldrM⇒⇓foldrA (foldrM-undefined φ) =
  ⇓foldrA-∷ ⇓foldrA-undefined (⇓transposeF-undefined φ)
⇓foldrM⇒⇓foldrA (foldrM-thunk φ₁ φ₂) =
  ⇓foldrA-∷ (⇓foldrA-thunk (⇓foldrM⇒⇓foldrA φ₁)) (⇓transposeF-thunk φ₂)

⇓foldrM : ∀ {v₁ v₂ c}
        → ⟦ t₃ ⟧ᵉ γ ∋ v₁
        → ⟦foldrM t₁ , t₂ ⟧ᵉ γ v₁ ∋ (v₂ , c)
        → ⟦ `foldrM t₁ t₂ t₃ ⟧ᵉ γ ∋ (v₂ , c)
⇓foldrM φ₁ φ₂ = ⇓foldrA φ₁ (⇓foldrM⇒⇓foldrA φ₂)

foldrM-lemma : ∀ {as b} {v : ⟦ τ ⟧ᵗ}
             → ⟦foldrM t₁ , t₂ ⟧ᵉ γ as ∋ b
             → ⟦foldrM subsume2 t₁ , ↑ᵗ t₂ ⟧ᵉ (γ ⸴ v) as ∋ b
foldrM-lemma (foldrM-[] φ)        = foldrM-[] (⇓weaken φ)
foldrM-lemma (foldrM-undefined φ) = foldrM-undefined (⇓subsume2 φ)
foldrM-lemma (foldrM-thunk φ₁ φ₂) = foldrM-thunk (foldrM-lemma φ₁) (⇓subsume2 φ₂)

----------------------
-- Type translation --
----------------------

⌊_⌋ᵗ : Explicit.Ty → Ty
⌊ `Bool   ⌋ᵗ = `Bool
⌊ `T A    ⌋ᵗ = `T ⌊ A ⌋ᵗ
⌊ `List A ⌋ᵗ = `ListA ⌊ A ⌋ᵗ

⌊_⌋ᶜ : Explicit.Ctx → Ctx
⌊ Γ ⌋ᶜ = List.map ⌊_⌋ᵗ Γ

--------------------------------------------------
-- Clairvoyance translation of values and terms --
--------------------------------------------------

ℂ⟦_⟧⌊_⌋ᵗ : (α : Explicit.Ty) → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
ℂ⟦_⟧⌊_⌋ᵗ′ : (α : Explicit.Ty) → ℂ.⟦ Explicit.`T α ⟧ᵗ → T ⟦ ⌊ α ⌋ᵗ ⟧ᵗ

-- Convert values.
ℂ⟦ `Bool   ⟧⌊ false   ⌋ᵗ = false
ℂ⟦ `Bool   ⟧⌊ true    ⌋ᵗ = true
ℂ⟦ `T α    ⟧⌊ v       ⌋ᵗ = ℂ⟦ α ⟧⌊ v ⌋ᵗ′
ℂ⟦ `List α ⟧⌊ []      ⌋ᵗ = []
ℂ⟦ `List α ⟧⌊ v₁ ∷ v₂ ⌋ᵗ = ℂ⟦ _ ⟧⌊ v₁ ⌋ᵗ ∷ ℂ⟦ _ ⟧⌊ v₂ ⌋ᵗ′

ℂ⟦ α ⟧⌊ undefined ⌋ᵗ′ = undefined
ℂ⟦ α ⟧⌊ thunk v   ⌋ᵗ′ = thunk ℂ⟦ α ⟧⌊ v ⌋ᵗ

ℂ⌊_⌋ᵗ : {α : Explicit.Ty} → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
ℂ⌊ v ⌋ᵗ = ℂ⟦ _ ⟧⌊ v ⌋ᵗ

ℂ⌊_⌋-map : ∀ {α} (xs : ℂ.⟦ `List α ⟧ᵗ) → ℂ⌊ xs ⌋ᵗ ≡ ListA.map ℂ⌊_⌋ᵗ xs
ℂ⌊ []            ⌋-map = refl
ℂ⌊ x ∷ undefined ⌋-map = refl
ℂ⌊ x ∷ thunk xs  ⌋-map = cong₂ _∷_ refl (cong thunk ℂ⌊ xs ⌋-map)

-- Convert evaluation contexts.
ℂ⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
ℂ⟦ Γ ⟧⌊ γ ⌋ᶜ = All.map⁺ (All.map ℂ⟦ _ ⟧⌊_⌋ᵗ γ)

ℂ⌊_⌋ᶜ : {Γ : Explicit.Ctx} → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
ℂ⌊ γ ⌋ᶜ = ℂ⟦ _ ⟧⌊ γ ⌋ᶜ

-- Convert terms.
ℂ⌊_⌋ᵉ : {Γ : Explicit.Ctx} {α : Explicit.Ty}
      → Explicit.Tm Γ α
      → ⌊ Γ ⌋ᶜ ⊢ `M ⌊ α ⌋ᵗ
ℂ⌊ Explicit.` x                      ⌋ᵉ = `return (` (∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x))
ℂ⌊ Explicit.`let t₁ `in t₂           ⌋ᵉ = ℂ⌊ t₁ ⌋ᵉ `>>= ℂ⌊ t₂ ⌋ᵉ
ℂ⌊ Explicit.`false                   ⌋ᵉ = `return `false
ℂ⌊ Explicit.`true                    ⌋ᵉ = `return `true
ℂ⌊ Explicit.`if t₁ `then t₂ `else t₃ ⌋ᵉ = ℂ⌊ t₁ ⌋ᵉ `>>= (`if (` zeroᵛ) `then ↑ᵗ ℂ⌊ t₂ ⌋ᵉ `else ↑ᵗ ℂ⌊ t₃ ⌋ᵉ)
ℂ⌊ Explicit.`[]                      ⌋ᵉ = `return `[]
ℂ⌊ t₁ Explicit.`∷ t₂                 ⌋ᵉ = ℂ⌊ t₁ ⌋ᵉ `>>= ↑ᵗ ℂ⌊ t₂ ⌋ᵉ `>>= `return (` (sucᵛ zeroᵛ) `∷ ` zeroᵛ)
ℂ⌊ Explicit.`foldr t₁ t₂ t₃          ⌋ᵉ = ℂ⌊ t₃ ⌋ᵉ `>>= `foldrM (subsume2 ℂ⌊ t₁ ⌋ᵉ) (↑ᵗ ℂ⌊ t₂ ⌋ᵉ) (` zeroᵛ)
ℂ⌊ Explicit.`tick t                  ⌋ᵉ = `tick ℂ⌊ t ⌋ᵉ
ℂ⌊ Explicit.`lazy t                  ⌋ᵉ = `fmap `thunk ℂ⌊ t ⌋ᵉ `? `return `undefined
ℂ⌊ Explicit.`force t                 ⌋ᵉ = ℂ⌊ t ⌋ᵉ `>>= `T-case (` zeroᵛ) (`return (` zeroᵛ)) `fail

mutual

  ℂ⌊_⌋ᵈ : ∀ {Γ α γ v c}
            {t : Explicit.Tm Γ α}
          → ℂ.⟦ t ⟧ᵉ γ ∋ (v , c)
          → ⟦ ℂ⌊ t ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ ∋ (ℂ⌊ v ⌋ᵗ , c)
  ℂ⌊_⌋ᵈ {γ = γ} (ℂ.` x) = ⇓return (⇓≡ (sym (All.app-lookup {Q = ⟦_⟧ᵗ} x γ ⌊_⌋ᵗ ℂ⌊_⌋ᵗ)) (⇓ ∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x))
  ℂ⌊ ℂ.`let φ₁ `in φ₂  ⌋ᵈ = ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ ℂ⌊ φ₂ ⌋ᵈ)
  ℂ⌊ ℂ.`false          ⌋ᵈ = ⇓return ⇓false
  ℂ⌊ ℂ.`true           ⌋ᵈ = ⇓return ⇓true
  ℂ⌊ ℂ.`if φ₁ `then φ₂ ⌋ᵈ = ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ (⇓if ⇓ zeroᵛ ⇓then ⇓weaken ℂ⌊ φ₂ ⌋ᵈ))
  ℂ⌊ ℂ.`if φ₁ `else φ₂ ⌋ᵈ = ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ (⇓if ⇓ zeroᵛ ⇓else ⇓weaken ℂ⌊ φ₂ ⌋ᵈ))
  ℂ⌊ ℂ.`[]             ⌋ᵈ = ⇓return ⇓[]          
  ℂ⌊_⌋ᵈ (ℂ._`∷_ {c₂ = c₂} φ₁ φ₂) =
    ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ (⇓cost≡ (+-identityʳ c₂)
      (⇓>>= (⇓>>=-intro (⇓weaken ℂ⌊ φ₂ ⌋ᵈ) (⇓return (⇓ sucᵛ zeroᵛ ⇓∷ ⇓ zeroᵛ))))))
  ℂ⌊_⌋ᵈ {γ = γ} {v = v} (ℂ.`foldr {t₁ = t₁} {t₂ = t₂} {as = as} {c₁ = c₁} {c₂ = c₂} φ₁ φ₂) =
    ⇓>>=
      (⇓>>=-intro
        ℂ⌊ φ₁ ⌋ᵈ
        (⇓foldrM (⇓ zeroᵛ)
          (foldrM-lemma
            (subst
              (λ xs → ⟦foldrM ℂ⌊ t₁ ⌋ᵉ , ℂ⌊ t₂ ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ xs ∋ (ℂ⌊ v ⌋ᵗ , c₂))
              (sym ℂ⌊ as ⌋-map) ℂ⌊foldr φ₂ ⌋ᵈ))))
  ℂ⌊ ℂ.`tick φ         ⌋ᵈ = ⇓tick ℂ⌊ φ ⌋ᵈ
  ℂ⌊ ℂ.`lazy-undefined ⌋ᵈ = ?r (⇓return ⇓undefined)
  ℂ⌊ ℂ.`lazy-thunk φ   ⌋ᵈ = ?l (⇓fmap `thunk thunk ⇓thunk ℂ⌊ φ ⌋ᵈ)
  ℂ⌊_⌋ᵈ {c = c} (ℂ.`force φ) =
    ⇓cost≡ (+-identityʳ c) (⇓>>= (⇓>>=-intro ℂ⌊ φ ⌋ᵈ (⇓T-case-thunk (⇓ zeroᵛ) (⇓return (⇓ zeroᵛ)))))

  ℂ⌊foldr_⌋ᵈ : ∀ {Γ α β}
                 {t₁ : Explicit.Tm (Γ ⸴ α ⸴ `T β) β}
                 {t₂ : Explicit.Tm Γ β}
                 {γ xs v c}
               → ℂ.⟦foldr t₁ , t₂ ⟧ᵉ γ xs ∋ (v , c)
               → ⟦foldrM ℂ⌊ t₁ ⌋ᵉ , ℂ⌊ t₂ ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ (ListA.map ℂ⌊_⌋ᵗ xs) ∋ (ℂ⌊ v ⌋ᵗ , c)
  ℂ⌊foldr ℂ.`foldr-[] φ        ⌋ᵈ = foldrM-[] ℂ⌊ φ ⌋ᵈ
  ℂ⌊foldr ℂ.`foldr-undefined φ ⌋ᵈ = foldrM-undefined ℂ⌊ φ ⌋ᵈ
  ℂ⌊foldr ℂ.`foldr-thunk φ₁ φ₂ ⌋ᵈ = foldrM-thunk ℂ⌊foldr φ₁ ⌋ᵈ ℂ⌊ φ₂ ⌋ᵈ

var-inv : ∀ {x : α ∈ᴸ Γ} {v} → ⟦ ` x ⟧ᵉ γ ∋ v → v ≡ All.lookup γ x
var-inv (⇓ x) = refl

-- ℂ⟦_⟧⌈_⌉ᵈ : ∀ {Γ α} (t : Explicit.Tm Γ α) {g v c} → ⟦ ℂ⌊ t ⌋ᵉ ⟧ᵉ ℂ⌊ g ⌋ᶜ ∋ (ℂ⌊ v ⌋ᵗ , c) → ℂ.⟦ t ⟧ᵉ g ∋ (v , c)
-- ℂ⟦_⟧⌈_⌉ᵈ (Explicit.` x) {g = g} {v = v} (⇓return φ) rewrite var-inv φ = {!subst (⟦ ` ∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x ⟧ᵉ ℂ⌊ g ⌋ᶜ ∋_) (var-inv φ) φ!}
-- ℂ⟦_⟧⌈_⌉ᵈ (Explicit.`let t₁ `in t₂) {c = c} φ with ⇑>>= c φ
-- ... | (v₁ , c₁ , φ₁ , φ₂ , φ₃) = ℂ.`let ℂ⟦ _ ⟧⌈ {!!} ⌉ᵈ `in {!!}
-- ℂ⟦_⟧⌈_⌉ᵈ Explicit.`false {v = false} (⇓return ⇓false) = ℂ.`false
-- ℂ⟦_⟧⌈_⌉ᵈ Explicit.`true  {v = true } (⇓return ⇓true ) = ℂ.`true
-- ℂ⟦_⟧⌈_⌉ᵈ (Explicit.`if t₁ `then t₂ `else t₃) {c = c₂} φ with ⇑>>= c₂ φ
-- ... | (v₁ , c₁ , φ₁ , φ₂ , φ₃) = {!!}
-- -- ... | false | ⇓if φ₂₁ ⇓else φ₂₂ = ℂ.`if {!φ₂₁!} `else {!!}
-- -- ... | true  | ⇓if φ₂₁ ⇓then φ₂₂ = {!!}
-- ℂ⟦_⟧⌈_⌉ᵈ Explicit.`[] {v = []} (⇓return ⇓[]) = ℂ.`[]
-- ℂ⟦_⟧⌈_⌉ᵈ (t₁ Explicit.`∷ t₂) φ = {!⇑>>= _ φ!}
-- ℂ⟦_⟧⌈_⌉ᵈ (Explicit.`foldr t t₁ t₂) φ = {!!}
-- ℂ⟦ Explicit.`tick t ⟧⌈ ⇓let φ₁ ⇓in ⇓proj₁ (⇓ _) ⇓, # 1 ⇓+ ⇓proj₂ (⇓ _) ⌉ᵈ = ℂ.`tick ℂ⟦ t ⟧⌈ φ₁ ⌉ᵈ
-- ℂ⟦ Explicit.`lazy t ⟧⌈ ?l φ ⌉ᵈ = let ψ = ⇑fmap `thunk {!thunk!} {!!} φ in {!!}
-- ℂ⟦_⟧⌈_⌉ᵈ (Explicit.`lazy t) {v = undefined} (?r (⇓return ⇓undefined)) = ℂ.`lazy-undefined
-- ℂ⟦_⟧⌈_⌉ᵈ (Explicit.`force t) φ = {!!}
-- -- ℂ⟦ Explicit.` x                     ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`let t₁ `in t₂          ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`false                  ⟧⌈ ⇓return φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`true                   ⟧⌈ ⇓return φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`if t `then t₁ `else t₂ ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`[]                     ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ t Explicit.`∷ t₁                 ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`foldr t t₁ t₂          ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`tick t                 ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`lazy t                 ⟧⌈ φ ⌉ᵈ = {!!}
-- -- ℂ⟦ Explicit.`force t                ⟧⌈ φ ⌉ᵈ = {!!}

-- ℂ⌊_⌋ᵈ : {Γ : ℂ.⟦ Γ ⟧ᶜ} {A : Explicit.Ty} ( {v : ℂ.⟦ A ⟧ᵗ} → ℂ.⟦ 

-- `assert_`in_ : Γ ⊢ `Bool → Γ ⊢ τ → Γ ⊢ τ
-- `assert t₁ `in t₂ = `if t₁ `then t₂ `else `fail

-- ⇓assert_⇓in_ : ∀ {v}
--              → ⟦ t₁ ⟧ᵉ g ∋ true
--              → ⟦ t₂ ⟧ᵉ g ∋ v
--              → ⟦ `assert t₁ `in t₂ ⟧ᵉ g ∋ v
-- ⇓assert_⇓in_ φ₁ φ₂ = ⇓if φ₁ ⇓then φ₂

-- `force : Γ ⊢ `T τ → Γ ⊢ τ
-- `force t = `T-case t (` zeroᵛ) `fail

-- ⇓force : ∀ {v}
--        → ⟦ t ⟧ᵉ γ ∋ thunk v
--        → ⟦ `force t ⟧ᵉ γ ∋ v
-- ⇓force φ = ⇓T-case-thunk φ (⇓ zeroᵛ)

-- `M : Ty → Ty
-- `M τ = τ `× `ℕ

-- _`>>=_ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → Γ ⊢ `M β
-- t₁ `>>= t₂ =
--   `let t₁ `in
--   `let (`let `proj₁ (` zeroᵛ) `in subsume1 t₂) `in
--   (`proj₁ (` zeroᵛ) `, (`proj₂ (` (sucᵛ zeroᵛ)) `+ `proj₂ (` zeroᵛ)))

-- _⇓>>=_ : ∀ {v₁ n₁ v₂ n₂}
--          → ⟦ t₁ ⟧ᵉ g ∋ (v₁ , n₁)
--          → ⟦ t₂ ⟧ᵉ (g ⸴ v₁) ∋ (v₂ , n₂)
--          → ⟦ t₁ `>>= t₂ ⟧ᵉ g ∋ (v₂ , n₁ + n₂)
-- φ₁ ⇓>>= φ₂ =
--   ⇓let φ₁ ⇓in
--   ⇓let (⇓let ⇓proj₁ (⇓ zeroᵛ) ⇓in ⇓subsume1 φ₂) ⇓in
--   ⇓proj₁ (⇓ zeroᵛ) ⇓, ⇓proj₂ (⇓ sucᵛ zeroᵛ) ⇓+ ⇓proj₂ (⇓ zeroᵛ)

-- `return : Γ ⊢ τ → Γ ⊢ `M τ
-- `return t = t `, 0

-- ⇓return : ∀ {t : Γ ⊢ α} {v}
--           → ⟦ t ⟧ᵉ g ∋ v
--           → ⟦ `return t ⟧ᵉ g ∋ (v , 0)
-- ⇓return φ = φ ⇓, # 0

-- `fmap : (∀ {Δ} → Δ ⊢ α → Δ ⊢ β) → Γ ⊢ `M α → Γ ⊢ `M β
-- `fmap f t = `let t `in f (`proj₁ (` zeroᵛ)) `, `proj₂ (` zeroᵛ)

-- -----------------
-- -- Translation --
-- -----------------

-- ⌊_⌋ᵗ : Explicit.Ty → Ty
-- ⌊ `Bool   ⌋ᵗ = `Bool
-- ⌊ `T α    ⌋ᵗ = `T ⌊ α ⌋ᵗ
-- ⌊ `List α ⌋ᵗ = `ListA ⌊ α ⌋ᵗ

-- ⌊_⌋ᶜ : Explicit.Ctx → Ctx
-- ⌊ γ ⌋ᶜ = List.map ⌊_⌋ᵗ γ

-- -- ℂ.⟦ t ⟧ g ∋ (v , n)
-- -- ↔
-- -- ⟦ ⌊t⌋ ⟧ ⌊g⌋ ∋ (v , n)

-- -- f(x) : Bool <-> P(x) : Prop
-- -- free <-> ∃.

-- ⌊_⌋ᵉ : ∀ {Γ τ} → Explicit.Tm Γ τ → ⌊ Γ ⌋ᶜ ⊢ `M ⌊ τ ⌋ᵗ
-- ⌊ Explicit.` x ⌋ᵉ                      = `return (` (∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x))
-- ⌊ Explicit.`let t₁ `in t₂ ⌋ᵉ           = ⌊ t₁ ⌋ᵉ `>>= ⌊ t₂ ⌋ᵉ
-- ⌊ Explicit.`false ⌋ᵉ                   = `return `false
-- ⌊ Explicit.`true ⌋ᵉ                    = `return `true
-- ⌊ Explicit.`if t₁ `then t₂ `else t₃ ⌋ᵉ =
--   ⌊ t₁ ⌋ᵉ `>>=
--   (`if ` zeroᵛ `then ↑ᵗ ⌊ t₂ ⌋ᵉ `else ↑ᵗ ⌊ t₃ ⌋ᵉ)
-- ⌊ Explicit.`[] ⌋ᵉ                      = `return `[]
-- ⌊ t₁ Explicit.`∷ t₂ ⌋ᵉ                 =
--   ⌊ t₁ ⌋ᵉ `>>=
--   ↑ᵗ ⌊ t₂ ⌋ᵉ `>>=
--   `return (` sucᵛ zeroᵛ `∷ ` zeroᵛ)
-- ⌊ Explicit.`foldr t₁ t₂ t₃ ⌋ᵉ          = ⌊ t₂ ⌋ᵉ
-- ⌊ Explicit.`tick t₁ ⌋ᵉ                 = `let ⌊ t₁ ⌋ᵉ `in `proj₁ (` zeroᵛ) `, 1 `+ `proj₂ (` zeroᵛ)
-- ⌊ Explicit.`lazy t₁ ⌋ᵉ                 = `fmap `thunk ⌊ t₁ ⌋ᵉ `? `return `undefined
-- ⌊ Explicit.`force t₁ ⌋ᵉ                = `fmap `force ⌊ t₁ ⌋ᵉ

-- ℂ⟦_⟧⌊_⌋ᵗ : (α : Explicit.Ty) → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
-- ℂ⟦ `Bool   ⟧⌊ false     ⌋ᵗ = false
-- ℂ⟦ `Bool   ⟧⌊ true      ⌋ᵗ = true
-- ℂ⟦ `T α    ⟧⌊ undefined ⌋ᵗ = undefined
-- ℂ⟦ `T α    ⟧⌊ thunk v   ⌋ᵗ = thunk ℂ⟦ α ⟧⌊ v ⌋ᵗ
-- ℂ⟦ `List α ⟧⌊ vs        ⌋ᵗ = foldrA (λ{ undefined vsT → undefined ∷ vsT ; (thunk v) vsT → thunk ℂ⟦ α ⟧⌊ v ⌋ᵗ ∷ vsT }) [] vs

-- ℂ⌊_⌋ᵗ : ∀ {α} → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
-- ℂ⌊ v ⌋ᵗ = ℂ⟦ _ ⟧⌊ v ⌋ᵗ

-- ℂ⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
-- ℂ⟦ Γ ⟧⌊ γ ⌋ᶜ = All.map⁺ (All.map ℂ⌊_⌋ᵗ γ)

-- ℂ⌊_⌋ᶜ : ∀ {Γ} → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
-- ℂ⌊ γ ⌋ᶜ = ℂ⟦ _ ⟧⌊ γ ⌋ᶜ

-- ⌊_⌋-ℂ : ∀ {Γ α g v c} {t : Explicit.Tm Γ α} → ℂ.⟦ t ⟧ᵉ g ∋ (v , c) → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ ℂ⌊ g ⌋ᶜ ∋ (ℂ⌊ v ⌋ᵗ , c)
-- ⌊ ℂ.` x             ⌋-ℂ = {!!}
-- ⌊ ℂ.`let φ₁ `in φ₂  ⌋-ℂ = ⌊ φ₁ ⌋-ℂ ⇓>>= ⌊ φ₂ ⌋-ℂ
-- ⌊ ℂ.`false          ⌋-ℂ = ⇓return ⇓false
-- ⌊ ℂ.`true           ⌋-ℂ = ⇓return ⇓true
-- ⌊ ℂ.`if φ₁ `else φ₂ ⌋-ℂ = ⌊ φ₁ ⌋-ℂ ⇓>>= (⇓if ⇓ zeroᵛ ⇓else ⇓weaken ⌊ φ₂ ⌋-ℂ)
-- ⌊ ℂ.`if φ₁ `then φ₂ ⌋-ℂ = ⌊ φ₁ ⌋-ℂ ⇓>>= (⇓if ⇓ zeroᵛ ⇓then ⇓weaken ⌊ φ₂ ⌋-ℂ)
-- ⌊ ℂ.`[]             ⌋-ℂ = ⇓return ⇓[]
-- ⌊ φ₁ ℂ.`∷ φ₂        ⌋-ℂ = {!!}
-- ⌊ ℂ.`foldr x x₁     ⌋-ℂ = {!!}
-- ⌊ ℂ.`tick φ         ⌋-ℂ = ⇓let ⌊ φ ⌋-ℂ ⇓in ⇓proj₁ (⇓ zeroᵛ) ⇓, # 1 ⇓+ ⇓proj₂ (⇓ zeroᵛ)
-- ⌊ ℂ.`lazy-undefined ⌋-ℂ = ?r (⇓return ⇓undefined)
-- ⌊ ℂ.`lazy-thunk φ   ⌋-ℂ = ?l (⇓let ⌊ φ ⌋-ℂ ⇓in (⇓thunk (⇓proj₁ (⇓ zeroᵛ))) ⇓, (⇓proj₂ (⇓ zeroᵛ)))
-- ⌊ ℂ.`force φ        ⌋-ℂ = ⇓let ⌊ φ ⌋-ℂ ⇓in (⇓force (⇓proj₁ (⇓ zeroᵛ))) ⇓, ⇓proj₂ (⇓ zeroᵛ)

-- ℂ-⌊_⌋ : ∀ {Γ α g v c} {t : Explicit.Tm Γ α} → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ ℂ⌊ g ⌋ᶜ ∋ (ℂ⌊ v ⌋ᵗ , c) → ℂ.⟦ t ⟧ᵉ g ∋ (v , c)
-- ℂ-⌊_⌋ = ?

-- ⟦_⟧ᵉₐ : ∀ {τ v} → 𝔻.⟦ τ ⟧≺ᵉ v → ⟦ ⌊ τ ⌋ᵗ ⟧ᵗ
-- ⟦_⟧ᵉₐ {Explicit.`Bool}   (𝔻.⟦_⟧≺ᵉ_.false) = false
-- ⟦_⟧ᵉₐ {Explicit.`Bool}   (𝔻.⟦_⟧≺ᵉ_.true) = true
-- ⟦_⟧ᵉₐ {Explicit.`T τ}    (𝔻.⟦_⟧≺ᵉ_.thunk v) = thunk ⟦ v ⟧ᵉₐ
-- ⟦_⟧ᵉₐ {Explicit.`T τ}    𝔻.⟦_⟧≺ᵉ_.undefined = undefined
-- ⟦_⟧ᵉₐ {Explicit.`List τ} 𝔻.⟦_⟧≺ᵉ_.[] = []
-- ⟦_⟧ᵉₐ {Explicit.`List τ} (v 𝔻.⟦_⟧≺ᵉ_.∷ v₁) = ⟦ v ⟧ᵉₐ ∷ ⟦ v₁ ⟧ᵉₐ

-- -- Ty⟦_⟧ₓ : Explicit.Ty → Type
-- -- Ty⟦ Explicit.`Bool ⟧ₓ   = Bool
-- -- Ty⟦ Explicit.`T τ ⟧ₓ    = Ty⟦ τ ⟧ₓ
-- -- Ty⟦ Explicit.`List τ ⟧ₓ = List Ty⟦ τ ⟧ₓ

-- -- reify : ∀ {τ} → Ty⟦ Ty⟦ τ ⟧ₜ ⟧ → Γ ⊢ Ty⟦ τ ⟧ₜ
-- -- reify {τ = Explicit.`Bool} false = `false
-- -- reify {τ = Explicit.`Bool} true = `true
-- -- reify {τ = Explicit.`T τ} (thunk x) = `thunk (reify  x)
-- -- reify {τ = Explicit.`T τ} undefined = `undefined
-- -- reify {τ = Explicit.`List τ} = foldrA (λ xT tT → T.rec (λ x → `thunk (reify x)) `undefined xT `∷ T.rec `thunk `undefined tT) `[]

-- -- reifyₐ : ∀ {τ} {v : Explicit.𝔼⟦ τ ⟧ᵗ} → 𝔻.⟦ τ ⟧≺ᵉ v → Γ ⊢ Ty⟦ τ ⟧ₜ
-- -- reifyₐ {Γ = Γ} a = reify {Γ = Γ} ⟦ a ⟧ᵉₐ

-- -- reifyₑ : ∀ {τ} → Explicit.𝔼⟦ τ ⟧ᵗ → Γ ⊢ Ty⟦ τ ⟧ₜ
-- -- reifyₑ {τ = Explicit.`Bool} false = `false
-- -- reifyₑ {τ = Explicit.`Bool} true = `true
-- -- reifyₑ {τ = Explicit.`T τ} v = `thunk (reifyₑ v)
-- -- reifyₑ {τ = Explicit.`List τ} v = foldr (λ v′ t → `thunk (reifyₑ v′) `∷ `thunk t) `[] v

-- reify : ∀ {τ} → ⟦ τ ⟧ᵗ → Γ ⊢ τ
-- reify {τ = `Bool} false = `false
-- reify {τ = `Bool} true = `true
-- reify {τ = τ₁ `× τ₂} (v₁ , v₂) = reify v₁ `, reify v₂
-- reify {τ = `T τ} (thunk v₁) = `thunk (reify v₁)
-- reify {τ = `T τ} undefined = `undefined
-- reify {τ = `ℕ} v = # v
-- reify {τ = `ListA τ} v = foldrA (λ v₁ t₂T → T.rec (`thunk ∘ reify) `undefined v₁ `∷ T.rec `thunk `undefined t₂T) `[] v

-- -- Translate a demand-language value.
-- ⟦_⟧ᵗ⌊_⌋ : (α : Explicit.Ty) → 𝔼.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
-- ⟦_⟧ᵗ⌊_⌋ `Bool v = v
-- ⟦_⟧ᵗ⌊_⌋ (`T α) v = thunk ⟦ α ⟧ᵗ⌊ v ⌋
-- ⟦_⟧ᵗ⌊_⌋ (`List α) vs = foldr (λ v vs′ → thunk ⟦ α ⟧ᵗ⌊ v ⌋ ∷ thunk vs′) [] vs

-- -- reifyₑ : ∀ {α} → 𝔼⟦ α ⟧ᵗ → Γ ⊢ Ty⟦ α ⟧ₜ
-- -- reifyₑ v = reify 𝔼⟦ _ ⟧ᵗ⌊ v ⌋

-- eval-reify : ∀ {α} (v : ⟦ α ⟧ᵗ) → ⟦ reify v ⟧ᵉ g ∋ v
-- eval-reify {α = `Bool} false = ⇓false
-- eval-reify {α = `Bool} true = ⇓true
-- eval-reify {α = α₁ `× α₂} (v₁ , v₂) = eval-reify v₁ ⇓, eval-reify v₂
-- eval-reify {α = `T α} (thunk v₁) = ⇓thunk (eval-reify v₁)
-- eval-reify {α = `T α} undefined = ⇓undefined
-- eval-reify {α = `ℕ} v = # v
-- eval-reify {α = `ListA α} v = {!!}

-- -- Translating and then reifying a demand-language
-- -- eval-reifyₑ : ∀ {α} (v : 𝔼⟦ α ⟧ᵗ) → ⟦ reifyₑ v ⟧ᵉ g ∋ 𝔼⟦ α ⟧ᵗ⌊ v ⌋
-- -- eval-reifyₑ {α = `Bool} v = {!reify!}
-- -- eval-reifyₑ {α = `T α} v = {!!}
-- -- eval-reifyₑ {α = `List α} v = {!!}

-- -- eval-reifyₐ : ∀ {α} {v : Explicit.𝔼⟦ α ⟧ᵗ} (a : 𝔻.⟦ α ⟧≺ᵉ v) {g} →
-- --   ⟦ reifyₐ {Γ = Γ} a ⟧ᵉ g ∋ ⟦ a ⟧ᵉₐ
-- -- eval-reifyₐ {α = Explicit.`Bool} {false} (𝔻.⟦_⟧≺ᵉ_.↓Bool) = `false
-- -- eval-reifyₐ {α = Explicit.`Bool} {true} (𝔻.⟦_⟧≺ᵉ_.↓Bool) = `true
-- -- eval-reifyₐ {α = Explicit.`T α} (𝔻.⟦_⟧≺ᵉ_.thunk a) = `thunk (eval-reifyₐ a)
-- -- eval-reifyₐ {α = Explicit.`T α} 𝔻.⟦_⟧≺ᵉ_.undefined = `undefined
-- -- eval-reifyₐ {α = Explicit.`List α} 𝔻.⟦_⟧≺ᵉ_.[] = `[]
-- -- eval-reifyₐ {α = Explicit.`List α} (a 𝔻.⟦_⟧≺ᵉ_.∷ a₁) = {!!}

-- -- demand₁ : ∀ {Γ α β}
-- --   {g : 𝔼.⟦ Γ ⸴ α ⟧ᶜ} →
-- --   (t : Explicit.Tm (Γ ⸴ α) β) →
-- --   𝔻.⟦ β ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ g →
-- --   Tick ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
-- -- demand₁ {g = _ ∷ _} t a = do
-- --   m ⸴ a′ ← 𝔻.⟦ t ⟧ᵉ _ a
-- --   return ⟦ a′ ⟧ᵉₐ

-- 𝔻⌊_⌋ᵗ : ∀ {Γ α β} →
--   Explicit.Tm (Γ ⸴ α) β →
--   𝔼.⟦ α ⟧ᵗ →
--   ⌊ Γ ⌋ᶜ ⸴ ⌊ β ⌋ᵗ ⊢ `M ⌊ α ⌋ᵗ
-- 𝔻⌊ t ⌋ᵗ v =
--    let outD = ` sucᵛ (sucᵛ zeroᵛ) in
--   `let reify ⟦ _ ⟧ᵗ⌊ v ⌋ `in
--    let a = ` sucᵛ zeroᵛ in
--   `let `free `in
--    let inD = `proj₁ (` zeroᵛ) in
--    let c = `proj₂ (` zeroᵛ) in
--   `assert inD `≲ a `in
--   `assert ↑ᵗ (subsume1 ⌊ t ⌋ᵉ) `≟ (outD `, c) `in
--   ` zeroᵛ

-- -- demand₂-if₁ : ∀ {Γ α β}
-- --   (t₁ : Explicit.Tm (Γ ⸴ α) Explicit.`Bool)
-- --   (t₂ t₃ : Explicit.Tm (Γ ⸴ α) β)
-- --   (v : 𝔼.⟦ α ⟧ᵗ)
-- --   g v′ →
-- --   ⟦ demand₂ (`if t₁ `then t₂ `else t₃) v ⟧ᵉ g v →


-- ⌊_⌋ᵃ : ∀ {α} {v : 𝔼.⟦ α ⟧ᵗ} → 𝔻.⟦ α ⟧≺ᵉ v → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
-- ⌊_⌋ᵃ {Explicit.`Bool} 𝔻.⟦_⟧≺ᵉ_.false = false
-- ⌊_⌋ᵃ {Explicit.`Bool} 𝔻.⟦_⟧≺ᵉ_.true = true
-- ⌊_⌋ᵃ {Explicit.`T α} (𝔻.⟦_⟧≺ᵉ_.thunk v) = thunk ⌊ v ⌋ᵃ
-- ⌊_⌋ᵃ {Explicit.`T α} 𝔻.⟦_⟧≺ᵉ_.undefined = undefined
-- ⌊_⌋ᵃ {Explicit.`List α} 𝔻.⟦_⟧≺ᵉ_.[] = []
-- ⌊_⌋ᵃ {Explicit.`List α} (v 𝔻.⟦_⟧≺ᵉ_.∷ v₁) = ⌊ v ⌋ᵃ ∷ ⌊ v₁ ⌋ᵃ

-- Ctx⟦_⟧ₑ : ∀ {Γ} {g : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ g → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
-- Ctx⟦_⟧ₑ {g = []} [] = []
-- Ctx⟦_⟧ₑ {g = g ⸴ px} (g′ ⸴ px′) = Ctx⟦_⟧ₑ g′ ⸴ ⌊ px′ ⌋ᵃ

-- -- theorem₁-∷ : ∀ {Γ α β}
-- --   (t₁ : Explicit.Tm (Γ ⸴ α) (Explicit.`T β))
-- --   (t₂ : Explicit.Tm (Γ ⸴ α) (Explicit.`T (Explicit.`List β)))
-- --   (g : 𝔼.⟦ Γ ⟧ᶜ)
-- --   (a : 𝔼.⟦ α ⟧ᵗ)
-- --   (outD₁ : 𝔻.⟦ Explicit.`T β ⟧≺ᵉ Explicit.E⟦ t₁ ⟧ᵉ (g , a))
-- --   (outD₂ : 𝔻.⟦ Explicit.`T (Explicit.`List β) ⟧≺ᵉ Explicit.E⟦ t₂ ⟧ᵉ (g , a)) →

-- lemma₁ : ∀ {α} {a : 𝔼.⟦ α ⟧ᵗ} (inD : 𝔻.⟦ α ⟧≺ᵉ a) →
--   Ty⟦ ⌊ α ⌋ᵗ ⟧[ ⟦ inD ⟧ᵉₐ ≲ ⟦ α ⟧ᵗ⌊ a ⌋ ]
-- lemma₁ {α} {a} 𝔻.false = false
-- lemma₁ {α} {a} 𝔻.true = true
-- lemma₁ {α} {a} (𝔻.thunk inD) = thunk (lemma₁ inD)
-- lemma₁ {α} {a} (𝔻.undefined) = undefined
-- lemma₁ {α} {a} 𝔻.[] = []
-- lemma₁ {α} {a} (inD₁ 𝔻.∷ inD₂) = lemma₁ inD₁ ∷ lemma₁ inD₂

-- ------------------------------------------------
-- -- Soundness with respect to demand semantics --
-- ------------------------------------------------

-- lemma₄ : ∀ {Γ α}
--            (x : α ∈ᴸ Γ)
--            (γ : 𝔼.⟦ Γ ⟧ᶜ)
--            (outD : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ Explicit.` x ⟧ᵉ γ)
--        → ⟦ ` ∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x ⟧ᵉ Ctx⟦ (𝔻.⊥⟦ Γ ⟧≺ᶜ γ) [ All.∈ᴸ⇒lookup∈ᴸtoList x ]≔ outD ⟧ₑ ∋ ⟦ outD ⟧ᵉₐ
-- lemma₄ zeroᵛ (g ⸴ px) outD = {!!}
-- lemma₄ (sucᵛ x) (g ⸴ px) outD = {!lemma₄ x g outD!}

-- lemma₃ :
--   ∀ {Γ α}
--     (t : Explicit.Tm Γ α)
--     {g : 𝔼.⟦ Γ ⟧ᶜ}
--     {g₁ g₂ : 𝔻.⟦ Γ ⟧≺ᶜ g}
--     {v}
--   → g₁ 𝔻.≤ᶜ g₂
--   → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ Ctx⟦ g₁ ⟧ₑ ∋ v
--   → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ Ctx⟦ g₂ ⟧ₑ ∋ v
-- lemma₃ t g₁≤g₂ φ = {!!}

-- -- First major theorem: starting with a certain output demand, evaluating
-- -- "backwards" in demand semantics and then evaluating "forwards" in logic
-- -- semantics yields the original output demand at the same cost.
-- lemma₂ :
--   ∀ {Γ α}
--     (t : Explicit.Tm Γ α)
--     (γ : 𝔼.⟦ Γ ⟧ᶜ)
--     (outD : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ) →
--     let (inDs , c) = 𝔻.⟦ t ⟧ᵉ γ outD
--     in ⟦ ⌊ t ⌋ᵉ ⟧ᵉ Ctx⟦ inDs ⟧ₑ ∋ (⟦ outD ⟧ᵉₐ , c)
-- lemma₂ {Γ = Γ} (Explicit.` x) γ outD = ⇓return {!All.universal!}
-- lemma₂ (Explicit.`let t₁ `in t₂) γ outD = {!!}
-- lemma₂ Explicit.`false γ false = ⇓return ⇓false
-- lemma₂ Explicit.`true γ true = ⇓return ⇓true
-- lemma₂ (Explicit.`if t₁ `then t₂ `else t₃) γ outD = {!!}
-- lemma₂ Explicit.`[] γ [] = ⇓return ⇓[]
-- lemma₂ (t₁ Explicit.`∷ t₂) γ (d₁ ∷ d₂) =
--   lemma₃ t₁ (𝔻.δ₁≤δ₁⊔δ₂ _ _) (lemma₂ t₁ γ d₁) ⇓>>= (⇓weaken (lemma₃ t₂ (𝔻.δ₂≤δ₁⊔δ₂ _ _) {!(lemma₂ t₂ γ d₂)!})) ⇓>>= {!!}
-- lemma₂ (Explicit.`foldr t t₁ t₂) γ outD = {!!}
-- lemma₂ (Explicit.`tick t) γ outD =
--   ⇓let lemma₂ t γ outD
--   ⇓in ⇓proj₁ (⇓ zeroᵛ) ⇓, # 1 ⇓+ ⇓proj₂ (⇓ zeroᵛ)
-- lemma₂ (Explicit.`lazy t) γ (thunk outD) =
--   ?l (⇓let (lemma₂ t γ outD) ⇓in ((⇓thunk (⇓proj₁ (⇓ zeroᵛ))) ⇓, (⇓proj₂ (⇓ zeroᵛ))))
-- lemma₂ (Explicit.`lazy t) γ undefined = ?r (⇓return ⇓undefined)
-- lemma₂ (Explicit.`force t) γ outD =
--   ⇓let lemma₂ t γ (thunk outD)
--   ⇓in ⇓T-case-thunk (⇓proj₁ (⇓ zeroᵛ)) (⇓ zeroᵛ) ⇓, ⇓proj₂ (⇓ zeroᵛ)

-- -- t : Γ ⊢ α
-- -- ⌊ t ⌋ : ⌊ Γ ⌋ ⊢ Tick ⌊ α ⌋

-- -- If you have a term t : Γ , α ⊢ β
-- -- and an evaluation context of shape Γ
-- -- and a value of type α
-- -- and a demand on β in context Γ , α
-- --
-- sound : ∀ {Γ α β}
--   {g : 𝔼.⟦ Γ ⟧ᶜ}
--   (a : 𝔼.⟦ α ⟧ᵗ)
--   (t : Explicit.Tm (Γ ⸴ α) β)
--   (outD : 𝔻.⟦ β ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ (g ⸴ a)) →
--   case 𝔻.⟦ t ⟧ᵉ (g ⸴ a) outD of λ{
--     ((inDs ⸴ inD) , c) → ⟦ 𝔻⌊ t ⌋ᵗ a ⟧ᵉ (Ctx⟦ inDs ⟧ₑ ⸴ ⟦ outD ⟧ᵉₐ) ∋ (⟦ inD ⟧ᵉₐ , c)
--   }
-- sound {α = α} {g = g} a t outD with 𝔻.⟦ t ⟧ᵉ (g ⸴ a) outD | inspect (𝔻.⟦ t ⟧ᵉ (g ⸴ a)) outD
-- ... | ((inDs ⸴ inD) , c) | [ φ ] =
--   ⇓let eval-reify ⟦ α ⟧ᵗ⌊ a ⌋ ⇓in
--   ⇓let ⇓free ⇓in
--   ⇓if ⇓≲-true (⇓proj₁ (⇓ zeroᵛ)) (⇓ sucᵛ zeroᵛ) (lemma₁ inD) ⇓then
--   ⇓if ⇓≟-true (⇓weaken (⇓exchange (⇓weaken {!!}))) (⇓ sucᵛ (sucᵛ zeroᵛ) ⇓, ⇓proj₂ (⇓ zeroᵛ)) ⇓then
--   (⇓ zeroᵛ)

-- -----------------------------------------------
-- -- Adequacy with respect to demand semantics --
-- -----------------------------------------------

-- -- theorem₂ : ∀ {Γ α β}
-- --   (t : Explicit.Tm (Γ ⸴ α) β)
-- --   (g : 𝔼.⟦ Γ ⟧ᶜ)
-- --   (v : 𝔼.⟦ α ⟧ᵗ)
-- --   (outD : Ty⟦ Ty⟦ β ⟧ₜ ⟧)
-- --   (inD : _) (c : ℕ) →
-- --   ⟦ demand₂ t v ⟧ᵉ ({!Ctx⟦ g ⟧ₑ!} ⸴ outD) ∋ (inD , c) →
-- --   runWriter (𝔻.⟦ t ⟧ᵉ {!!} {!!}) ≡ (c , {!!})
-- -- theorem₂ = {!!}

-- -- theorem₂ : ∀ {α β}
-- --   (t : Explicit.Tm ([] ⸴ α) β)
-- --   (g : 𝔼.⟦ [] ⟧ᶜ)
-- --   (v : 𝔼.⟦ α ⟧ᵗ)
-- --   (outD : 𝔻.⟦ β ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ ([] ⸴ v))
-- --   (inD : _) (c : ℕ) →
-- --   ⟦ demand₂ t v ⟧ᵉ ([] ⸴ ⌊ outD ⌋ᵃ) ∋ (⌊ inD ⌋ᵃ , c) →
-- --   𝔻.⟦ t ⟧ᵉ ([] ⸴ v) outD ≡ ([] ⸴ inD , c)
-- -- theorem₂ (Explicit.` x₄) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ (Explicit.`let t `in t₁) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ Explicit.`false g v 𝔻.⟦_⟧≺ᵉ_.↓Bool inD c (`let x `in (`let `free `in (`if `true (`proj₁ (` .zeroᵛ)) (` .(sucᵛ zeroᵛ)) x₅ `then (`if `≟-true (`false `, # .0) (` .(sucᵛ (sucᵛ zeroᵛ)) `, `proj₂ (` .zeroᵛ)) `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ Explicit.`true g v outD inD c (`let x `in (`let `free `in (`if `true x₂ x₄ x₅ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ (Explicit.`if t `then t₁ `else t₂) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ Explicit.`[] g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ (t Explicit.`∷ t₁) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ (Explicit.`foldr t t₁ t₂) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ (Explicit.`tick t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ (Explicit.`lazy t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- -- theorem₂ (Explicit.`force t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
