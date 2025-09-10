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
open import Data.Nat
  as ℕ
  using (ℕ; _+_)
open import Data.Product
  as Σ
open import Data.Product.Properties
  as Σ
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
  α α₁ α₂ β τ τ₁ τ₂ : Ty

Ctx : Type
Ctx = List Ty

variable
  Γ Δ : Ctx

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

  _`∷_             : Γ ⊢ `T τ
                   → Γ ⊢ `T (`ListA τ)
                   → Γ ⊢ `ListA τ

  `foldrA          : Γ ⸴ `T α ⸴ β ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ `ListA α
                   → Γ ⊢ β

  `free            : Γ ⊢ τ

  _`?_             : Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ τ

  `fail            : Γ ⊢ τ

variable
  t t₁ t₂ t₃ : Γ ⊢ τ

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

Ty-≡-dec : DecidableEquality ⟦ τ ⟧ᵗ
Ty-≡-dec {`Bool}    = Bool._≟_
Ty-≡-dec {α `× β}   = Σ.≡-dec Ty-≡-dec Ty-≡-dec
Ty-≡-dec {`T τ}     = T.≡-dec Ty-≡-dec
Ty-≡-dec {`ℕ}       = ℕ._≟_
Ty-≡-dec {`ListA τ} = ListA.≡-dec Ty-≡-dec

⟦_⟧ᶜ : Ctx → Type
⟦_⟧ᶜ = All ⟦_⟧ᵗ

variable
  g γ : ⟦ Γ ⟧ᶜ

---------------
-- Renamings --
---------------

infix 2 _→ʳ_
_→ʳ_ : Ctx → Ctx → Type
Γ →ʳ Δ = ∀ {τ} → τ ∈ᴸ Γ → τ ∈ᴸ Δ

variable
  ρ : Γ →ʳ Δ

↑ʳ_ : Γ →ʳ Δ → Γ ⸴ τ →ʳ Δ ⸴ τ
↑ʳ_ ρ zeroᵛ    = zeroᵛ
↑ʳ_ ρ (sucᵛ x) = sucᵛ (ρ x)

infixr -1 _$ʳ_
_$ʳ_ : Γ →ʳ Δ → Γ ⊢ τ → Δ ⊢ τ
ρ $ʳ ` x                      = ` ρ x
ρ $ʳ `let t₁ `in t₂           = `let (ρ $ʳ t₁) `in (↑ʳ ρ $ʳ t₂)
ρ $ʳ `false                   = `false
ρ $ʳ `true                    = `true
ρ $ʳ `if t₁ `then t₂ `else t₃ = `if (ρ $ʳ t₁) `then ρ $ʳ t₂ `else (ρ $ʳ t₃)
ρ $ʳ t₁ `≟ t₂                 = (ρ $ʳ t₁) `≟ (ρ $ʳ t₂)
ρ $ʳ t₁ `≲ t₂                 = (ρ $ʳ t₁) `≲ (ρ $ʳ t₂)
ρ $ʳ t₁ `, t₂                 = (ρ $ʳ t₁) `, (ρ $ʳ t₂)
ρ $ʳ `proj₁ t₁                  = `proj₁ (ρ $ʳ t₁)
ρ $ʳ `proj₂ t₁                  = `proj₂ (ρ $ʳ t₁)
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

↑ᵗ_ : Γ ⊢ α → Γ ⸴ τ ⊢ α
↑ᵗ_ = (sucᵛ $ʳ_)

exchange : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
exchange t = ρ′ $ʳ t
  where
    ρ′ : α ∈ᴸ Γ ⸴ τ₁ ⸴ τ₂ → α ∈ᴸ Γ ⸴ τ₂ ⸴ τ₁
    ρ′ (here px) = there (here px)
    ρ′ (sucᵛ (here px)) = here px
    ρ′ (sucᵛ (sucᵛ p)) = there (there p)

-- A common special-case context manipulation.
subsume1 : Γ ⸴ τ₁ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
subsume1 t = exchange (↑ᵗ t)

-------------------
-- Substitutions --
-------------------

infix 4 _→ˢ_
_→ˢ_ : Ctx → Ctx → Type
_→ˢ_ Γ Δ = ∀ {τ} → τ ∈ᴸ Γ → Δ ⊢ τ

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
σ $ˢ `proj₁ t₁                  = `proj₁ (σ $ˢ t₁)
σ $ˢ `proj₂ t₁                  = `proj₂ (σ $ˢ t₁)
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
  _∷_ : ∀ {v₁ vs₁ v₂ vs₂} → Ty⟦ `T α ⟧[ v₁ ≲ v₂ ] → Ty⟦ `T (`ListA α) ⟧[ vs₁ ≲ vs₂ ] →
    Ty⟦ `ListA α ⟧[ v₁ ∷ vs₁ ≲ v₂ ∷ vs₂ ]

Ty⟦_⟧[_≴_] : ∀ α → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type
Ty⟦ α ⟧[ v₁ ≴ v₂ ] = ¬ Ty⟦ α ⟧[ v₁ ≲ v₂ ]

----------------
-- Evaluation --
----------------

data foldrA⟦_,_,_⟧
    (P : ⟦ Γ ⸴ `T α ⸴ β ⟧ᶜ → ⟦ β ⟧ᵗ → Type)
    (e : ⟦ β ⟧ᵗ) :
    T (ListA ⟦ α ⟧ᵗ) →
    ⟦ Γ ⟧ᶜ →
    ⟦ β ⟧ᵗ →
    Type where
  foldrA-undefined : foldrA⟦ P , e , undefined ⟧ g ∋ e
  foldrA-[]        : foldrA⟦ P , e , thunk []  ⟧ g ∋ e
  foldrA-∷         : ∀ {b b′ a as} →
    foldrA⟦ P , e , as ⟧ g ∋ b →
    P (g ⸴ a ⸴ b) ∋ b′ →
    foldrA⟦ P , e , thunk (a ∷ as) ⟧ g ∋ b′

data ⟦_⟧ᵉ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ᶜ → ⟦ τ ⟧ᵗ → Type where
  ⇓_                : (x : τ ∈ᴸ Γ) → ⟦ ` x ⟧ᵉ g (All.lookup g x)
  ⇓let_⇓in_         : ∀ {v₁ v₂} →
    ⟦ t₁ ⟧ᵉ g ∋ v₁ →
    ⟦ t₂ ⟧ᵉ (g ⸴ v₁) ∋ v₂ →
    ⟦ `let t₁ `in t₂ ⟧ᵉ g ∋ v₂
  ⇓false            : ⟦ `false ⟧ᵉ g ∋ false
  ⇓true             : ⟦ `true ⟧ᵉ g ∋ true
  ⇓if_⇓else_ : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ false →
    ⟦ t₃ ⟧ᵉ g ∋ v →
    ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g ∋ v
  ⇓if_⇓then_ : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ true →
    ⟦ t₂ ⟧ᵉ g ∋ v →
    ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g ∋ v
  ⇓≟-true : {v : ⟦ τ ⟧ᵗ} →
    ⟦ t₁ ⟧ᵉ g ∋ v →
    ⟦ t₂ ⟧ᵉ g ∋ v →
    ⟦ t₁ `≟ t₂ ⟧ᵉ g ∋ true
  ⇓≟-false : {v₁ v₂ : ⟦ τ ⟧ᵗ}
           → ⟦ t₁ ⟧ᵉ g ∋ v₁
           → ⟦ t₂ ⟧ᵉ g ∋ v₂
           → v₁ ≢ v₂
           → ⟦ t₁ `≟ t₂ ⟧ᵉ g ∋ false
  ⇓≲-true : {v₁ v₂ : ⟦ τ ⟧ᵗ} →
    ⟦ t₁ ⟧ᵉ g ∋ v₁ →
    ⟦ t₂ ⟧ᵉ g ∋ v₂ →
    Ty⟦ τ ⟧[ v₁ ≲ v₂ ] →
    ⟦ t₁ `≲ t₂ ⟧ᵉ g ∋ true
  ⇓≲-false : {v₁ v₂ : ⟦ τ ⟧ᵗ}
           → ⟦ t₁ ⟧ᵉ g ∋ v₁
           → ⟦ t₂ ⟧ᵉ g ∋ v₂
           → Ty⟦ τ ⟧[ v₁ ≴ v₂ ]
           → ⟦ t₁ `≲ t₂ ⟧ᵉ g ∋ false
  _⇓,_              : ∀ {v₁ v₂} →
    ⟦ t₁ ⟧ᵉ g ∋ v₁ →
    ⟦ t₂ ⟧ᵉ g ∋ v₂ →
    ⟦ t₁ `, t₂ ⟧ᵉ g ∋ (v₁ , v₂)
  ⇓proj1 : ∀ {v} →
    ⟦ t ⟧ᵉ g ∋ v →
    ⟦ `proj₁ t ⟧ᵉ g ∋ proj₁ v
  ⇓proj2 : ∀ {v}
    → ⟦ t ⟧ᵉ g v
    → ⟦ `proj₂ t ⟧ᵉ g ∋ proj₂ v
  ⇓undefined : ⟦ `undefined {τ = τ} ⟧ᵉ g ∋ undefined
  ⇓thunk : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ v →
    ⟦ `thunk t₁ ⟧ᵉ g ∋ thunk v
  ⇓T-case-undefined : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ undefined →
    ⟦ t₃ ⟧ᵉ g ∋ v →
    ⟦ `T-case t₁ t₂ t₃ ⟧ᵉ g ∋ v
  ⇓T-case-thunk     : ∀ {v₁ v₂} →
    ⟦ t₁ ⟧ᵉ g ∋ thunk v₁ →
    ⟦ t₂ ⟧ᵉ (g ⸴ v₁) ∋ v₂ →
    ⟦ `T-case t₁ t₂ t₃ ⟧ᵉ g ∋ v₂
  #_                : ∀ n → ⟦ # n ⟧ᵉ g n
  _⇓+_              : ∀ {n₁ n₂} →
    ⟦ t₁ ⟧ᵉ g ∋ n₁ →
    ⟦ t₂ ⟧ᵉ g ∋ n₂ →
    ⟦ t₁ `+ t₂ ⟧ᵉ g ∋ (n₁ + n₂)
  ⇓[]               : ∀ {τ} → ⟦_⟧ᵉ {τ = `ListA τ} `[] g []
  _⇓∷_              : ∀ {x xs} → ⟦ t₁ ⟧ᵉ g x → ⟦ t₂ ⟧ᵉ g xs → ⟦ t₁ `∷ t₂ ⟧ᵉ g (x ∷ xs)
  ⇓foldrA           : ∀ {e xs b} →
    ⟦ t₂ ⟧ᵉ g e →
    ⟦ t₃ ⟧ᵉ g xs →
    foldrA⟦ ⟦ t₁ ⟧ᵉ , e , thunk xs ⟧ g ∋ b →
    ⟦ `foldrA t₁ t₂ t₃ ⟧ᵉ g b
  ⇓free             : ∀ {v : ⟦ α ⟧ᵗ} → ⟦ `free ⟧ᵉ g v
  ?l                : ∀ {x} → ⟦ t₁ ⟧ᵉ g x → ⟦ t₁ `? t₂ ⟧ᵉ g x
  ?r                : ∀ {x} → ⟦ t₂ ⟧ᵉ g x → ⟦ t₁ `? t₂ ⟧ᵉ g x

-- eval-true : ∀ {v₁ v₂ : Ty⟦ α ⟧} →
--   ⟦ t₁ ⟧ᵉ g ∋ v₁ →
--   ⟦ t₂ ⟧ᵉ g ∋ v₂ →
--   Ty⟦ α ⟧[ v₁ ≲ v₂ ] →
--   ⟦ t₁ `≲ t₂ ⟧ᵉ g true
-- eval-true {v₁ = v₁} {v₂} p q r with v₁ ≲? v₂
-- ... | yes s = subst (⟦ _ `≲ _ ⟧ᵉ _) (dec-true _ s) (eval-≲ p q)
-- ... | no s = contradiction r s

⇓weaken :
  ∀ {Γ α τ} {t : Γ ⊢ τ} {g : ⟦ Γ ⟧ᶜ} {a : ⟦ α ⟧ᵗ}
    {v : ⟦ τ ⟧ᵗ}
  → ⟦ t ⟧ᵉ g v
  → ⟦ ↑ᵗ t ⟧ᵉ (g ⸴ a) v
⇓weaken (⇓ x) = ⇓ sucᵛ x
⇓weaken (⇓let φ₁ ⇓in φ₂) = ⇓let ⇓weaken φ₁ ⇓in {!!}
⇓weaken ⇓false = ⇓false
⇓weaken ⇓true = ⇓true
⇓weaken (⇓if φ₁ ⇓else φ₂) = ⇓if ⇓weaken φ₁ ⇓else ⇓weaken φ₂
⇓weaken (⇓if φ₁ ⇓then φ₂) = ⇓if ⇓weaken φ₁ ⇓then ⇓weaken φ₂
⇓weaken (⇓≟-true φ₁ φ₂) = ⇓≟-true (⇓weaken φ₁) (⇓weaken φ₂)
⇓weaken (⇓≟-false φ₁ φ₂ ψ) = {!!}
⇓weaken (⇓≲-true φ₁ φ₂ ψ) = ⇓≲-true (⇓weaken φ₁) (⇓weaken φ₂) ψ
⇓weaken (⇓≲-false φ₁ φ₂ ψ) = {!!}
⇓weaken (φ₁ ⇓, φ₂) = ⇓weaken φ₁ ⇓, ⇓weaken φ₂
⇓weaken (⇓proj1 φ₁) = ⇓proj1 (⇓weaken φ₁)
⇓weaken (⇓proj2 φ₁) = ⇓proj2 (⇓weaken φ₁)
⇓weaken ⇓undefined = ⇓undefined
⇓weaken (⇓thunk φ₁) = ⇓thunk (⇓weaken φ₁)
⇓weaken (⇓T-case-thunk φ₁ φ₂) = ⇓T-case-thunk (⇓weaken φ₁) {!⇓weaken φ₂!}
⇓weaken (⇓T-case-undefined φ₁ φ₂) = ⇓T-case-undefined (⇓weaken φ₁) (⇓weaken φ₂)
⇓weaken (# n) = # n
⇓weaken (φ₁ ⇓+ φ₂) = ⇓weaken φ₁ ⇓+ ⇓weaken φ₂
⇓weaken ⇓[] = ⇓[]
⇓weaken (φ₁ ⇓∷ φ₂) = ⇓weaken φ₁ ⇓∷ ⇓weaken φ₂
⇓weaken (⇓foldrA e e₁ x) = {!!}
⇓weaken ⇓free = ⇓free
⇓weaken (?l φ₁) = ?l (⇓weaken φ₁)
⇓weaken (?r φ₁) = ?r (⇓weaken φ₁)

⇓exchange :
  ∀ {Γ α τ₁ τ₂} {t : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α} {g : ⟦ Γ ⟧ᶜ} {a : ⟦ α ⟧ᵗ}
    {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ}
  → ⟦ t ⟧ᵉ (g ⸴ v₁ ⸴ v₂) a
  → ⟦ exchange t ⟧ᵉ (g ⸴ v₂ ⸴ v₁) a
⇓exchange = {!!}

⇓subsume1 : {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
          → ⟦ t ⟧ᵉ (g ⸴ v₁) ∋ v
          → ⟦ subsume1 t ⟧ᵉ (g ⸴ v₂ ⸴ v₁) ∋ v
⇓subsume1 = {!!}

-----------------
-- Translation --
-----------------

⌊_⌋ᵗ : Explicit.Ty → Ty
⌊ `Bool ⌋ᵗ   = `Bool
⌊ `T α ⌋ᵗ    = `T ⌊ α ⌋ᵗ
⌊ `List α ⌋ᵗ = `ListA ⌊ α ⌋ᵗ

⌊_⌋ᶜ : Explicit.Ctx → Ctx
⌊ γ ⌋ᶜ = List.map ⌊_⌋ᵗ γ

`assert_`in_ : Γ ⊢ `Bool → Γ ⊢ τ → Γ ⊢ τ
`assert t₁ `in t₂ = `if t₁ `then t₂ `else `fail

⇓assert_⇓in_ : ∀ {v} →
  ⟦ t₁ ⟧ᵉ g ∋ true →
  ⟦ t₂ ⟧ᵉ g ∋ v →
  ⟦ `assert t₁ `in t₂ ⟧ᵉ g ∋ v
⇓assert_⇓in_ δ₁ δ₂ = ⇓if δ₁ ⇓then δ₂

`force : Γ ⊢ `T τ → Γ ⊢ τ
`force t = `T-case t (` zeroᵛ) `fail

`M : Ty → Ty
`M τ = τ `× `ℕ

_`>>=_ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → Γ ⊢ `M β
t₁ `>>= t₂ =
  `let t₁ `in
  `let (`let `proj₁ (` zeroᵛ) `in subsume1 t₂) `in
  (`proj₁ (` zeroᵛ) `, (`proj₂ (` (sucᵛ zeroᵛ)) `+ `proj₂ (` zeroᵛ)))

-- Evaluation for >>=.
_⇓>>=_ : ∀ {v₁ n₁ v₂ n₂}
         → ⟦ t₁ ⟧ᵉ g ∋ (v₁ , n₁)
         → ⟦ t₂ ⟧ᵉ (g ⸴ v₁) ∋ (v₂ , n₂)
         → ⟦ t₁ `>>= t₂ ⟧ᵉ g ∋ (v₂ , n₁ + n₂)
φ₁ ⇓>>= φ₂ =
  ⇓let φ₁ ⇓in
  ⇓let (⇓let ⇓proj1 (⇓ zeroᵛ) ⇓in ⇓subsume1 φ₂) ⇓in
  ⇓proj1 (⇓ zeroᵛ) ⇓, ⇓proj2 (⇓ sucᵛ zeroᵛ) ⇓+ ⇓proj2 (⇓ zeroᵛ)

`fmap : (∀ {Δ} → Δ ⊢ α → Δ ⊢ β) → Γ ⊢ `M α → Γ ⊢ `M β
`fmap f t = `let t `in f (`proj₁ (` zeroᵛ)) `, `proj₂ (` zeroᵛ)

-- ⇓fmap : {f : ∀ {Δ} → Δ ⊢ α → Δ ⊢ β} → (∀ {Δ} (δ : ⟦ Δ ⟧ᶜ) (t : Δ ⊢ α) → ⟦ f t ⟧ᵉ δ ∋ v) →

`return : Γ ⊢ τ → Γ ⊢ `M τ
`return t = t `, 0

-- Evaluation for return.
⇓return : ∀ {t : Γ ⊢ α} {v}
          → ⟦ t ⟧ᵉ g ∋ v
          → ⟦ `return t ⟧ᵉ g ∋ (v , 0)
⇓return φ = φ ⇓, # 0

-- ℂ.⟦ t ⟧ g ∋ (v , n)
-- ↔
-- ⟦ ⌊t⌋ ⟧ ⌊g⌋ ∋ (v , n)

-- f(x) : Bool <-> P(x) : Prop
-- free <-> ∃.

⌊_⌋ᵉ : ∀ {Γ τ} → Explicit.Tm Γ τ → ⌊ Γ ⌋ᶜ ⊢ `M ⌊ τ ⌋ᵗ
⌊ Explicit.` x ⌋ᵉ                      = `return (` (∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x))
⌊ Explicit.`let t₁ `in t₂ ⌋ᵉ           = ⌊ t₁ ⌋ᵉ `>>= ⌊ t₂ ⌋ᵉ
⌊ Explicit.`false ⌋ᵉ                   = `return `false
⌊ Explicit.`true ⌋ᵉ                    = `return `true
⌊ Explicit.`if t₁ `then t₂ `else t₃ ⌋ᵉ =
  ⌊ t₁ ⌋ᵉ `>>=
  (`if ` zeroᵛ `then ↑ᵗ ⌊ t₂ ⌋ᵉ `else ↑ᵗ ⌊ t₃ ⌋ᵉ)
⌊ Explicit.`[] ⌋ᵉ                      = `return `[]
⌊ t₁ Explicit.`∷ t₂ ⌋ᵉ                 =
  ⌊ t₁ ⌋ᵉ `>>=
  ↑ᵗ ⌊ t₂ ⌋ᵉ `>>=
  `return (` sucᵛ zeroᵛ `∷ ` zeroᵛ)
⌊ Explicit.`foldr t₁ t₂ t₃ ⌋ᵉ          = ⌊ t₂ ⌋ᵉ
⌊ Explicit.`tick t₁ ⌋ᵉ                 = `let ⌊ t₁ ⌋ᵉ `in `proj₁ (` zeroᵛ) `, 1 `+ `proj₂ (` zeroᵛ)
⌊ Explicit.`lazy t₁ ⌋ᵉ                 = `fmap `thunk ⌊ t₁ ⌋ᵉ `? `return `undefined
⌊ Explicit.`force t₁ ⌋ᵉ                = `fmap `force ⌊ t₁ ⌋ᵉ

ℂ⟦_⟧⌊_⌋ᵗ : (α : Explicit.Ty) → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
ℂ⟦ `Bool   ⟧⌊ false     ⌋ᵗ = false
ℂ⟦ `Bool   ⟧⌊ true      ⌋ᵗ = true
ℂ⟦ `T α    ⟧⌊ undefined ⌋ᵗ = undefined
ℂ⟦ `T α    ⟧⌊ thunk v   ⌋ᵗ = thunk ℂ⟦ α ⟧⌊ v ⌋ᵗ
ℂ⟦ `List α ⟧⌊ vs        ⌋ᵗ = foldrA (λ{ undefined vsT → undefined ∷ vsT ; (thunk v) vsT → thunk ℂ⟦ α ⟧⌊ v ⌋ᵗ ∷ vsT }) [] vs

ℂ⌊_⌋ᵗ : ∀ {α} → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
ℂ⌊ v ⌋ᵗ = ℂ⟦ _ ⟧⌊ v ⌋ᵗ

ℂ⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
ℂ⟦ Γ ⟧⌊ γ ⌋ᶜ = All.map⁺ (All.map ℂ⌊_⌋ᵗ γ)

ℂ⌊_⌋ᶜ : ∀ {Γ} → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
ℂ⌊ γ ⌋ᶜ = ℂ⟦ _ ⟧⌊ γ ⌋ᶜ

⌊_⌋-ℂ : ∀ {Γ α g v c} {t : Explicit.Tm Γ α} → ℂ.⟦ t ⟧ᵉ g ∋ (v , c) → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ ℂ⌊ g ⌋ᶜ ∋ (ℂ⌊ v ⌋ᵗ , c)
⌊ ℂ.` x ⌋-ℂ = {!!}
⌊ ℂ.`let φ₁ `in φ₂ ⌋-ℂ = {!!}
⌊ ℂ.`false ⌋-ℂ = ⇓return ⇓false
⌊ ℂ.`true ⌋-ℂ = ⇓return ⇓true
⌊ ℂ.`if φ₁ `else φ₂ ⌋-ℂ = ⌊ φ₁ ⌋-ℂ ⇓>>= (⇓if ⇓ zeroᵛ ⇓else ⇓weaken ⌊ φ₂ ⌋-ℂ)
⌊ ℂ.`if φ₁ `then φ₂ ⌋-ℂ = ⌊ φ₁ ⌋-ℂ ⇓>>= (⇓if ⇓ zeroᵛ ⇓then ⇓weaken ⌊ φ₂ ⌋-ℂ)
⌊ ℂ.`[] ⌋-ℂ = ⇓return ⇓[]
⌊ x ℂ.`∷ x₁ ⌋-ℂ = {!!}
⌊ ℂ.`foldr x x₁ ⌋-ℂ = {!!}
⌊ ℂ.`tick φ₁ ⌋-ℂ = {!!}
⌊ ℂ.`lazy-undefined ⌋-ℂ = ?r (⇓return ⇓undefined)
⌊ ℂ.`lazy-thunk φ₁ ⌋-ℂ = ?l {!!}
⌊ ℂ.`force φ₁ ⌋-ℂ = {!!}

-- ⌊_⌋ᶜ : ∀ {Γ} → Explicit.Ctx⟦ Γ ⟧ₑ → Ctx⟦ 

⟦_⟧ᵉₐ : ∀ {τ v} → 𝔻.⟦ τ ⟧≺ᵉ v → ⟦ ⌊ τ ⌋ᵗ ⟧ᵗ
⟦_⟧ᵉₐ {Explicit.`Bool}   (𝔻.⟦_⟧≺ᵉ_.false) = false
⟦_⟧ᵉₐ {Explicit.`Bool}   (𝔻.⟦_⟧≺ᵉ_.true) = true
⟦_⟧ᵉₐ {Explicit.`T τ}    (𝔻.⟦_⟧≺ᵉ_.thunk v) = thunk ⟦ v ⟧ᵉₐ 
⟦_⟧ᵉₐ {Explicit.`T τ}    𝔻.⟦_⟧≺ᵉ_.undefined = undefined
⟦_⟧ᵉₐ {Explicit.`List τ} 𝔻.⟦_⟧≺ᵉ_.[] = []
⟦_⟧ᵉₐ {Explicit.`List τ} (v 𝔻.⟦_⟧≺ᵉ_.∷ v₁) = ⟦ v ⟧ᵉₐ ∷ ⟦ v₁ ⟧ᵉₐ

-- Ty⟦_⟧ₓ : Explicit.Ty → Type
-- Ty⟦ Explicit.`Bool ⟧ₓ   = Bool
-- Ty⟦ Explicit.`T τ ⟧ₓ    = Ty⟦ τ ⟧ₓ
-- Ty⟦ Explicit.`List τ ⟧ₓ = List Ty⟦ τ ⟧ₓ

-- reify : ∀ {τ} → Ty⟦ Ty⟦ τ ⟧ₜ ⟧ → Γ ⊢ Ty⟦ τ ⟧ₜ
-- reify {τ = Explicit.`Bool} false = `false
-- reify {τ = Explicit.`Bool} true = `true
-- reify {τ = Explicit.`T τ} (thunk x) = `thunk (reify  x)
-- reify {τ = Explicit.`T τ} undefined = `undefined
-- reify {τ = Explicit.`List τ} = foldrA (λ xT tT → T.rec (λ x → `thunk (reify x)) `undefined xT `∷ T.rec `thunk `undefined tT) `[]

-- reifyₐ : ∀ {τ} {v : Explicit.𝔼⟦ τ ⟧ᵗ} → 𝔻.⟦ τ ⟧≺ᵉ v → Γ ⊢ Ty⟦ τ ⟧ₜ
-- reifyₐ {Γ = Γ} a = reify {Γ = Γ} ⟦ a ⟧ᵉₐ

-- reifyₑ : ∀ {τ} → Explicit.𝔼⟦ τ ⟧ᵗ → Γ ⊢ Ty⟦ τ ⟧ₜ
-- reifyₑ {τ = Explicit.`Bool} false = `false
-- reifyₑ {τ = Explicit.`Bool} true = `true
-- reifyₑ {τ = Explicit.`T τ} v = `thunk (reifyₑ v)
-- reifyₑ {τ = Explicit.`List τ} v = foldr (λ v′ t → `thunk (reifyₑ v′) `∷ `thunk t) `[] v

reify : ∀ {τ} → ⟦ τ ⟧ᵗ → Γ ⊢ τ
reify {τ = `Bool} false = `false
reify {τ = `Bool} true = `true
reify {τ = τ₁ `× τ₂} (v₁ , v₂) = reify v₁ `, reify v₂
reify {τ = `T τ} (thunk v₁) = `thunk (reify v₁)
reify {τ = `T τ} undefined = `undefined
reify {τ = `ℕ} v = # v
reify {τ = `ListA τ} v = foldrA (λ v₁ t₂T → T.rec (`thunk ∘ reify) `undefined v₁ `∷ T.rec `thunk `undefined t₂T) `[] v

-- Translate a demand-language value.
⟦_⟧ᵗ⌊_⌋ : (α : Explicit.Ty) → 𝔼.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
⟦_⟧ᵗ⌊_⌋ `Bool v = v
⟦_⟧ᵗ⌊_⌋ (`T α) v = thunk ⟦ α ⟧ᵗ⌊ v ⌋
⟦_⟧ᵗ⌊_⌋ (`List α) vs = foldr (λ v vs′ → thunk ⟦ α ⟧ᵗ⌊ v ⌋ ∷ thunk vs′) [] vs

-- reifyₑ : ∀ {α} → 𝔼⟦ α ⟧ᵗ → Γ ⊢ Ty⟦ α ⟧ₜ
-- reifyₑ v = reify 𝔼⟦ _ ⟧ᵗ⌊ v ⌋

eval-reify : ∀ {α} (v : ⟦ α ⟧ᵗ) → ⟦ reify v ⟧ᵉ g ∋ v
eval-reify {α = `Bool} false = ⇓false
eval-reify {α = `Bool} true = ⇓true
eval-reify {α = α₁ `× α₂} (v₁ , v₂) = eval-reify v₁ ⇓, eval-reify v₂
eval-reify {α = `T α} (thunk v₁) = ⇓thunk (eval-reify v₁)
eval-reify {α = `T α} undefined = ⇓undefined
eval-reify {α = `ℕ} v = # v
eval-reify {α = `ListA α} v = {!!}

-- Translating and then reifying a demand-language
-- eval-reifyₑ : ∀ {α} (v : 𝔼⟦ α ⟧ᵗ) → ⟦ reifyₑ v ⟧ᵉ g ∋ 𝔼⟦ α ⟧ᵗ⌊ v ⌋
-- eval-reifyₑ {α = `Bool} v = {!reify!}
-- eval-reifyₑ {α = `T α} v = {!!}
-- eval-reifyₑ {α = `List α} v = {!!}

-- eval-reifyₐ : ∀ {α} {v : Explicit.𝔼⟦ α ⟧ᵗ} (a : 𝔻.⟦ α ⟧≺ᵉ v) {g} →
--   ⟦ reifyₐ {Γ = Γ} a ⟧ᵉ g ∋ ⟦ a ⟧ᵉₐ
-- eval-reifyₐ {α = Explicit.`Bool} {false} (𝔻.⟦_⟧≺ᵉ_.↓Bool) = `false
-- eval-reifyₐ {α = Explicit.`Bool} {true} (𝔻.⟦_⟧≺ᵉ_.↓Bool) = `true
-- eval-reifyₐ {α = Explicit.`T α} (𝔻.⟦_⟧≺ᵉ_.thunk a) = `thunk (eval-reifyₐ a)
-- eval-reifyₐ {α = Explicit.`T α} 𝔻.⟦_⟧≺ᵉ_.undefined = `undefined
-- eval-reifyₐ {α = Explicit.`List α} 𝔻.⟦_⟧≺ᵉ_.[] = `[]
-- eval-reifyₐ {α = Explicit.`List α} (a 𝔻.⟦_⟧≺ᵉ_.∷ a₁) = {!!}

demand₁ : ∀ {Γ α β}
  {g : 𝔼.⟦ Γ ⸴ α ⟧ᶜ} →
  (t : Explicit.Tm (Γ ⸴ α) β) →
  𝔻.⟦ β ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ g →
  Tick ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
demand₁ {g = _ ∷ _} t a = do
  m ⸴ a′ ← 𝔻.⟦ t ⟧ᵉ _ a
  return ⟦ a′ ⟧ᵉₐ

demand₂ : ∀ {Γ α β} →
  Explicit.Tm (Γ ⸴ α) β →
  𝔼.⟦ α ⟧ᵗ →
  ⌊ Γ ⌋ᶜ ⸴ ⌊ β ⌋ᵗ ⊢ `M ⌊ α ⌋ᵗ
demand₂ t v =
   let outD = ` sucᵛ (sucᵛ zeroᵛ) in
  `let reify ⟦ _ ⟧ᵗ⌊ v ⌋ `in
   let a = ` sucᵛ zeroᵛ in
  `let `free `in
   let inD = `proj₁ (` zeroᵛ) in
   let c = `proj₂ (` zeroᵛ) in
  `assert inD `≲ a `in
  `assert ↑ᵗ (subsume1 ⌊ t ⌋ᵉ) `≟ (outD `, c) `in
  ` zeroᵛ

-- demand₂-if₁ : ∀ {Γ α β}
--   (t₁ : Explicit.Tm (Γ ⸴ α) Explicit.`Bool)
--   (t₂ t₃ : Explicit.Tm (Γ ⸴ α) β)
--   (v : 𝔼.⟦ α ⟧ᵗ)
--   g v′ →
--   ⟦ demand₂ (`if t₁ `then t₂ `else t₃) v ⟧ᵉ g v →


⌊_⌋ᵃ : ∀ {α} {v : 𝔼.⟦ α ⟧ᵗ} → 𝔻.⟦ α ⟧≺ᵉ v → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
⌊_⌋ᵃ {Explicit.`Bool} 𝔻.⟦_⟧≺ᵉ_.false = false
⌊_⌋ᵃ {Explicit.`Bool} 𝔻.⟦_⟧≺ᵉ_.true = true
⌊_⌋ᵃ {Explicit.`T α} (𝔻.⟦_⟧≺ᵉ_.thunk v) = thunk ⌊ v ⌋ᵃ
⌊_⌋ᵃ {Explicit.`T α} 𝔻.⟦_⟧≺ᵉ_.undefined = undefined
⌊_⌋ᵃ {Explicit.`List α} 𝔻.⟦_⟧≺ᵉ_.[] = []
⌊_⌋ᵃ {Explicit.`List α} (v 𝔻.⟦_⟧≺ᵉ_.∷ v₁) = ⌊ v ⌋ᵃ ∷ ⌊ v₁ ⌋ᵃ

Ctx⟦_⟧ₑ : ∀ {Γ} {g : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ g → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
Ctx⟦_⟧ₑ {g = []} [] = []
Ctx⟦_⟧ₑ {g = g ⸴ px} (g′ ⸴ px′) = Ctx⟦_⟧ₑ g′ ⸴ ⌊ px′ ⌋ᵃ

-- theorem₁-∷ : ∀ {Γ α β}
--   (t₁ : Explicit.Tm (Γ ⸴ α) (Explicit.`T β))
--   (t₂ : Explicit.Tm (Γ ⸴ α) (Explicit.`T (Explicit.`List β)))
--   (g : 𝔼.⟦ Γ ⟧ᶜ)
--   (a : 𝔼.⟦ α ⟧ᵗ)
--   (outD₁ : 𝔻.⟦ Explicit.`T β ⟧≺ᵉ Explicit.E⟦ t₁ ⟧ᵉ (g , a))
--   (outD₂ : 𝔻.⟦ Explicit.`T (Explicit.`List β) ⟧≺ᵉ Explicit.E⟦ t₂ ⟧ᵉ (g , a)) →

lemma₁ : ∀ {α} {a : 𝔼.⟦ α ⟧ᵗ} (inD : 𝔻.⟦ α ⟧≺ᵉ a) →
  Ty⟦ ⌊ α ⌋ᵗ ⟧[ ⟦ inD ⟧ᵉₐ ≲ ⟦ α ⟧ᵗ⌊ a ⌋ ]
lemma₁ {α} {a} 𝔻.false = false
lemma₁ {α} {a} 𝔻.true = true
lemma₁ {α} {a} (𝔻.thunk inD) = thunk (lemma₁ inD)
lemma₁ {α} {a} (𝔻.undefined) = undefined
lemma₁ {α} {a} 𝔻.[] = []
lemma₁ {α} {a} (inD₁ 𝔻.∷ inD₂) = lemma₁ inD₁ ∷ lemma₁ inD₂

------------------------------------------------
-- Soundness with respect to demand semantics --
------------------------------------------------

lemma₄ : ∀ {Γ α}
           (x : α ∈ᴸ Γ)
           (γ : 𝔼.⟦ Γ ⟧ᶜ)
           (outD : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ Explicit.` x ⟧ᵉ γ)
       → ⟦ ` ∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x ⟧ᵉ Ctx⟦ (𝔻.⊥⟦ Γ ⟧≺ᶜ γ) [ All.∈ᴸ⇒lookup∈ᴸtoList x ]≔ outD ⟧ₑ ∋ ⟦ outD ⟧ᵉₐ
lemma₄ zeroᵛ (g ⸴ px) outD = {!!}
lemma₄ (sucᵛ x) (g ⸴ px) outD = {!lemma₄ x g outD!}

lemma₃ :
  ∀ {Γ α}
    (t : Explicit.Tm Γ α)
    {g : 𝔼.⟦ Γ ⟧ᶜ}
    {g₁ g₂ : 𝔻.⟦ Γ ⟧≺ᶜ g}
    {v}
  → g₁ 𝔻.≤ᶜ g₂
  → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ Ctx⟦ g₁ ⟧ₑ ∋ v
  → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ Ctx⟦ g₂ ⟧ₑ ∋ v
lemma₃ t g₁≤g₂ φ = {!!}

-- First major theorem: starting with a certain output demand, evaluating
-- "backwards" in demand semantics and then evaluating "forwards" in logic
-- semantics yields the original output demand at the same cost.
lemma₂ :
  ∀ {Γ α}
    (t : Explicit.Tm Γ α)
    (γ : 𝔼.⟦ Γ ⟧ᶜ)
    (outD : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ) →
    let (inDs , c) = 𝔻.⟦ t ⟧ᵉ γ outD
    in ⟦ ⌊ t ⌋ᵉ ⟧ᵉ Ctx⟦ inDs ⟧ₑ ∋ (⟦ outD ⟧ᵉₐ , c)
lemma₂ {Γ = Γ} (Explicit.` x) γ outD = ⇓return {!All.universal!}
lemma₂ (Explicit.`let t₁ `in t₂) γ outD = {!!}
lemma₂ Explicit.`false γ false = ⇓return ⇓false
lemma₂ Explicit.`true γ true = ⇓return ⇓true
lemma₂ (Explicit.`if t₁ `then t₂ `else t₃) γ outD = {!!}
lemma₂ Explicit.`[] γ [] = ⇓return ⇓[]
lemma₂ (t₁ Explicit.`∷ t₂) γ (d₁ ∷ d₂) =
  lemma₃ t₁ (𝔻.δ₁≤δ₁⊔δ₂ _ _) (lemma₂ t₁ γ d₁) ⇓>>= (⇓weaken (lemma₃ t₂ (𝔻.δ₂≤δ₁⊔δ₂ _ _) {!(lemma₂ t₂ γ d₂)!})) ⇓>>= {!!}
lemma₂ (Explicit.`foldr t t₁ t₂) γ outD = {!!}
lemma₂ (Explicit.`tick t) γ outD =
  ⇓let lemma₂ t γ outD
  ⇓in ⇓proj1 (⇓ zeroᵛ) ⇓, # 1 ⇓+ ⇓proj2 (⇓ zeroᵛ)
lemma₂ (Explicit.`lazy t) γ (thunk outD) =
  ?l (⇓let (lemma₂ t γ outD) ⇓in ((⇓thunk (⇓proj1 (⇓ zeroᵛ))) ⇓, (⇓proj2 (⇓ zeroᵛ))))
lemma₂ (Explicit.`lazy t) γ undefined = ?r (⇓return ⇓undefined)
lemma₂ (Explicit.`force t) γ outD =
  ⇓let lemma₂ t γ (thunk outD)
  ⇓in ⇓T-case-thunk (⇓proj1 (⇓ zeroᵛ)) (⇓ zeroᵛ) ⇓, ⇓proj2 (⇓ zeroᵛ)

-- t : Γ ⊢ α
-- ⌊ t ⌋ : ⌊ Γ ⌋ ⊢ Tick ⌊ α ⌋

-- If you have a term t : Γ , α ⊢ β
-- and an evaluation context of shape Γ
-- and a value of type α
-- and a demand on β in context Γ , α
-- 
sound : ∀ {Γ α β}
  {g : 𝔼.⟦ Γ ⟧ᶜ}
  (a : 𝔼.⟦ α ⟧ᵗ)
  (t : Explicit.Tm (Γ ⸴ α) β)
  (outD : 𝔻.⟦ β ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ (g ⸴ a)) →
  case 𝔻.⟦ t ⟧ᵉ (g ⸴ a) outD of λ{
    ((inDs ⸴ inD) , c) → ⟦ demand₂ t a ⟧ᵉ (Ctx⟦ inDs ⟧ₑ ⸴ ⟦ outD ⟧ᵉₐ) ∋ (⟦ inD ⟧ᵉₐ , c)
  }
sound {α = α} {g = g} a t outD with 𝔻.⟦ t ⟧ᵉ (g ⸴ a) outD | inspect (𝔻.⟦ t ⟧ᵉ (g ⸴ a)) outD
... | ((inDs ⸴ inD) , c) | [ φ ] =
  ⇓let eval-reify ⟦ α ⟧ᵗ⌊ a ⌋ ⇓in
  ⇓let ⇓free ⇓in
  ⇓if ⇓≲-true (⇓proj1 (⇓ zeroᵛ)) (⇓ sucᵛ zeroᵛ) (lemma₁ inD) ⇓then
  ⇓if ⇓≟-true (⇓weaken (⇓exchange (⇓weaken {!!}))) (⇓ sucᵛ (sucᵛ zeroᵛ) ⇓, ⇓proj2 (⇓ zeroᵛ)) ⇓then
  (⇓ zeroᵛ)

-----------------------------------------------
-- Adequacy with respect to demand semantics --
-----------------------------------------------

-- theorem₂ : ∀ {Γ α β}
--   (t : Explicit.Tm (Γ ⸴ α) β)
--   (g : 𝔼.⟦ Γ ⟧ᶜ)
--   (v : 𝔼.⟦ α ⟧ᵗ)
--   (outD : Ty⟦ Ty⟦ β ⟧ₜ ⟧)
--   (inD : _) (c : ℕ) →
--   ⟦ demand₂ t v ⟧ᵉ ({!Ctx⟦ g ⟧ₑ!} ⸴ outD) ∋ (inD , c) →
--   runWriter (𝔻.⟦ t ⟧ᵉ {!!} {!!}) ≡ (c , {!!})
-- theorem₂ = {!!}

-- theorem₂ : ∀ {α β}
--   (t : Explicit.Tm ([] ⸴ α) β)
--   (g : 𝔼.⟦ [] ⟧ᶜ)
--   (v : 𝔼.⟦ α ⟧ᵗ)
--   (outD : 𝔻.⟦ β ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ ([] ⸴ v))
--   (inD : _) (c : ℕ) →
--   ⟦ demand₂ t v ⟧ᵉ ([] ⸴ ⌊ outD ⌋ᵃ) ∋ (⌊ inD ⌋ᵃ , c) →
--   𝔻.⟦ t ⟧ᵉ ([] ⸴ v) outD ≡ ([] ⸴ inD , c)
-- theorem₂ (Explicit.` x₄) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Explicit.`let t `in t₁) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ Explicit.`false g v 𝔻.⟦_⟧≺ᵉ_.↓Bool inD c (`let x `in (`let `free `in (`if `true (`proj1 (` .zeroᵛ)) (` .(sucᵛ zeroᵛ)) x₅ `then (`if `≟-true (`false `, # .0) (` .(sucᵛ (sucᵛ zeroᵛ)) `, `proj2 (` .zeroᵛ)) `then (` .zeroᵛ))))) = {!!}
-- theorem₂ Explicit.`true g v outD inD c (`let x `in (`let `free `in (`if `true x₂ x₄ x₅ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Explicit.`if t `then t₁ `else t₂) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ Explicit.`[] g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (t Explicit.`∷ t₁) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Explicit.`foldr t t₁ t₂) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Explicit.`tick t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Explicit.`lazy t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Explicit.`force t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
