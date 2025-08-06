module LogicalLaziness.Language.Demand where

-- open import Algebra
-- open import Data.Bool
--   hiding (T; _≤_)
-- open import Relation.Binary.PropositionalEquality
-- open import Algebra.Bundles.Raw
-- open import Effect.Functor
-- open import Effect.Applicative
-- open import Effect.Monad
-- open import Effect.Monad.Identity
-- open import Effect.Monad.Writer
-- open import Effect.Monad.Writer.Transformer
-- open import Data.Product
--   hiding (_<*>_)
-- open import Data.Product.Properties
-- open import Data.Product.Relation.Binary.Pointwise.NonDependent
--   as ×
-- open import Data.Nat
--   as ℕ
--   hiding (_⊔_; _≤_)
-- open import Data.Nat.Properties
--   as ℕ
-- open import Data.List
-- open import Data.List.Relation.Unary.Any
-- open import Data.List.Relation.Unary.All as All
-- open import Data.List.Relation.Unary.All.Properties as All

open import Algebra
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Product
  hiding (_<*>_)
open import Data.Product.Properties
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  as ×
open import Data.Nat
  as ℕ
open import Data.Nat.Properties
  as ℕ
open import Data.List
open import Data.List.Relation.Unary.All
  as All
open import Effect.Monad.Writer

open import LogicalLaziness.Base

data Ty : Type where
  `Bool : Ty
  `T    : Ty → Ty
  `List : Ty → Ty

private
  variable
    α β τ : Ty

Ctx : Type
Ctx = List Ty

private
  variable
    Γ : Ctx

-----------
-- Terms --
-----------

infix  1.59  `_
infixr 1.55  _`∷_
infix  1.505 `if_`then_`else_
infix  1.50  `let_`in_

infix 4 _⊢_
data _⊢_ : Ctx → Ty → Type where
  `_               : α ∈ᴸ Γ
                   → Γ ⊢ α

  `let_`in_        : Γ ⊢ α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β

  `false           : Γ ⊢ `Bool
  `true            : Γ ⊢ `Bool

  `if_`then_`else_ : Γ ⊢ `Bool
                   → Γ ⊢ α
                   → Γ ⊢ α
                   → Γ ⊢ α

  `[]              : Γ ⊢ `List α

  _`∷_             : Γ ⊢ `T α
                   → Γ ⊢ `T (`List α)
                   → Γ ⊢ `List α

  `foldr           : Γ ⸴ `T α ⸴ `T β ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ `List α → Γ ⊢ β

  `tick            : Γ ⊢ α
                   → Γ ⊢ α

  `lazy            : Γ ⊢ α
                   → Γ ⊢ `T α

  `force           : Γ ⊢ `T α
                   → Γ ⊢ α

private
  variable
    t : Γ ⊢ α

Tm = _⊢_

𝔼⟦_⟧ᵗ : Ty → Type
𝔼⟦ `Bool   ⟧ᵗ = Bool
𝔼⟦ `T τ    ⟧ᵗ = 𝔼⟦ τ ⟧ᵗ
𝔼⟦ `List τ ⟧ᵗ = List 𝔼⟦ τ ⟧ᵗ

𝔼⟦_⟧ᶜ : Ctx → Type
𝔼⟦_⟧ᶜ = All 𝔼⟦_⟧ᵗ

private
  variable
    g : 𝔼⟦ Γ ⟧ᶜ

------------------------
-- Forward evaluation --
------------------------

𝔼⟦_⟧ᵉ : Γ ⊢ τ → 𝔼⟦ Γ ⟧ᶜ → 𝔼⟦ τ ⟧ᵗ

𝔼⟦if_,_⟧ᵉ : Γ ⊢ α
          → Γ ⊢ α
          → 𝔼⟦ Γ ⟧ᶜ
          → Bool
          → 𝔼⟦ α ⟧ᵗ

𝔼⟦foldr_,_⟧ᵉ : Γ ⸴ `T α ⸴ `T β ⊢ β
             → Γ ⊢ β
             → 𝔼⟦ Γ ⟧ᶜ
             → List 𝔼⟦ α ⟧ᵗ
             → 𝔼⟦ β ⟧ᵗ

𝔼⟦ ` x                      ⟧ᵉ g = All.lookup g x
𝔼⟦ `let t₁ `in t₂           ⟧ᵉ g = let a = 𝔼⟦ t₁ ⟧ᵉ g in 𝔼⟦ t₂ ⟧ᵉ (g ⸴ a)
𝔼⟦ `false                   ⟧ᵉ g = false
𝔼⟦ `true                    ⟧ᵉ g = true
𝔼⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g = 𝔼⟦if t₂ , t₃ ⟧ᵉ g (𝔼⟦ t₁ ⟧ᵉ g)
𝔼⟦ `[]                      ⟧ᵉ g = []
𝔼⟦ t₁ `∷ t₂                 ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g ∷ 𝔼⟦ t₂ ⟧ᵉ g
𝔼⟦ `foldr t₁ t₂ t₃          ⟧ᵉ g = 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g (𝔼⟦ t₃ ⟧ᵉ g)
𝔼⟦ `tick t₁                 ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g
𝔼⟦ `lazy t₁                 ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g
𝔼⟦ `force t₁                ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g

𝔼⟦if t₁ , t₂ ⟧ᵉ g b = if b then 𝔼⟦ t₁ ⟧ᵉ g else 𝔼⟦ t₂ ⟧ᵉ g

𝔼⟦foldr t₁ , t₂ ⟧ᵉ g = foldr (λ a b → 𝔼⟦ t₁ ⟧ᵉ (g ⸴ a ⸴ b)) (𝔼⟦ t₂ ⟧ᵉ g)

--------------------
-- Approximations --
--------------------

infix 4 𝔻⟦_⟧ᵗ≺_ 𝔻⟦_⟧ᶜ≺_

-- `𝔻⟦ τ ⟧ᵗ≺ v` describes the set of partial values in `τ` that approximate the
-- total value `v`.
infixr 5 _∷_
data 𝔻⟦_⟧ᵗ≺_ : (α : Ty) → 𝔼⟦ α ⟧ᵗ → Type where
  ↓Bool      : {v : Bool} → 𝔻⟦ `Bool ⟧ᵗ≺ v
  thunk     : {α : Ty} {v : 𝔼⟦ α ⟧ᵗ} → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ `T α ⟧ᵗ≺ v
  undefined : {α : Ty} {v : 𝔼⟦ α ⟧ᵗ} → 𝔻⟦ `T α ⟧ᵗ≺ v
  []        : {α : Ty} → 𝔻⟦ `List α ⟧ᵗ≺ []
  _∷_       : {α : Ty} {v : 𝔼⟦ α ⟧ᵗ} {vs : List 𝔼⟦ α ⟧ᵗ} →
    𝔻⟦ `T α ⟧ᵗ≺ v →
    𝔻⟦ `T (`List α) ⟧ᵗ≺ vs →
    𝔻⟦ `List α ⟧ᵗ≺ v ∷ vs

-- `𝔻⟦ Γ ⟧ᶜ≺ g` is the set of evaluation contexts of shape `Γ` that elementwise
-- approximate `g`.
𝔻⟦_⟧ᶜ≺_ : (Γ : Ctx) → 𝔼⟦ Γ ⟧ᶜ → Type
𝔻⟦ Γ ⟧ᶜ≺ g = All (uncurry 𝔻⟦_⟧ᵗ≺_) (All.toList g)

-- Least upper bounds of approximations.
infixl 6 _⊔ᵉ_
_⊔ᵉ_ : {v : 𝔼⟦ α ⟧ᵗ} → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ α ⟧ᵗ≺ v
↓Bool      ⊔ᵉ      ↓Bool = ↓Bool
thunk x   ⊔ᵉ thunk y   = thunk (x ⊔ᵉ y)
thunk x   ⊔ᵉ undefined = thunk x
undefined ⊔ᵉ thunk y   = thunk y
undefined ⊔ᵉ undefined = undefined
[]        ⊔ᵉ []        = []
(x ∷ x₁)  ⊔ᵉ (y ∷ y₁)  = x ⊔ᵉ y ∷ x₁ ⊔ᵉ y₁

-- Pairwise joins of approximation contexts.
infixl 6 _⊔ᶜ_
_⊔ᶜ_ : 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ Γ ⟧ᶜ≺ g
bs₁ ⊔ᶜ bs₂ = All.zipWith (uncurry _⊔ᵉ_) (bs₁ , bs₂)

-- Least approximation of a total value.
⊥ᵉ : ∀ τ (v : 𝔼⟦ τ ⟧ᵗ) → 𝔻⟦ τ ⟧ᵗ≺ v
⊥ᵉ `Bool     _       = ↓Bool
⊥ᵉ (`T _)    _       = undefined
⊥ᵉ (`List _) []      = []
⊥ᵉ (`List _) (_ ∷ _) = undefined ∷ undefined

-- Least approximation of a total evaluation context.
⊥ᶜ : 𝔻⟦ Γ ⟧ᶜ≺ g
⊥ᶜ = universal (uncurry ⊥ᵉ) _

infixl 6 _⊔ᵐ_
_⊔ᵐ_ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Tick (𝔻⟦ Γ ⟧ᶜ≺ g)
m₁ ⊔ᵐ m₂ = _⊔ᶜ_ <$> m₁ <*> m₂

⊥ᵐ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g)
⊥ᵐ = return ⊥ᶜ

--------------------------
-- Backwards evaluation --
--------------------------

𝔻⟦_⟧ᵉ :
  (t : Γ ⊢ τ)
  (g : 𝔼⟦ Γ ⟧ᶜ) →
  𝔻⟦ τ ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g →
  Tick (𝔻⟦ Γ ⟧ᶜ≺ g)

𝔻⟦if_,_⟧ᵉ : ∀ {Γ α}
  (t₁ t₂ : Γ ⊢ α)
  (g : 𝔼⟦ Γ ⟧ᶜ)
  (v : Bool) →
  𝔻⟦ α ⟧ᵗ≺ 𝔼⟦if t₁ , t₂ ⟧ᵉ g v →
  Tick (𝔻⟦ Γ ⟧ᶜ≺ g)
𝔻⟦if t₁ , t₂ ⟧ᵉ g v d
 with v
... | false = 𝔻⟦ t₂ ⟧ᵉ g d
... | true  = 𝔻⟦ t₁ ⟧ᵉ g d

𝔻⟦foldr_,_⟧ᵉ : ∀ {Γ α β}
  (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) →
  (t₂ : Γ ⊢ β) →
  (g : 𝔼⟦ Γ ⟧ᶜ) →
  (xs : List 𝔼⟦ α ⟧ᵗ) →
  𝔻⟦ β ⟧ᵗ≺ 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g xs →
  Tick (𝔻⟦ Γ ⟧ᶜ≺ g × 𝔻⟦ `List α ⟧ᵗ≺ xs)
𝔻⟦foldr_,_⟧′ᵉ : ∀ {Γ α β}
  (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) →
  (t₂ : Γ ⊢ β) →
  (g : 𝔼⟦ Γ ⟧ᶜ) →
  (xs : List 𝔼⟦ α ⟧ᵗ) →
  𝔻⟦ `T β ⟧ᵗ≺ 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g xs →
  Tick (𝔻⟦ Γ ⟧ᶜ≺ g × 𝔻⟦ `T (`List α) ⟧ᵗ≺ xs)

𝔻⟦ ` x ⟧ᵉ g d = return (⊥ᶜ [ ∈ᴸ⇒lookup∈ᴸtoList x ]≔ d)
𝔻⟦ `let t₁ `in t₂ ⟧ᵉ g d₂ = do
  d₁ ∷ g₂′ ← 𝔻⟦ t₂ ⟧ᵉ (g ⸴ 𝔼⟦ t₁ ⟧ᵉ g) d₂
  g₁′ ← 𝔻⟦ t₁ ⟧ᵉ g d₁
  return (g₁′ ⊔ᶜ g₂′)
𝔻⟦ `false ⟧ᵉ g d = return ⊥ᶜ
𝔻⟦ `true ⟧ᵉ g d = return ⊥ᶜ
𝔻⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g d = 𝔻⟦ t₁ ⟧ᵉ g ↓Bool ⊔ᵐ 𝔻⟦if t₂ , t₃ ⟧ᵉ g (𝔼⟦ t₁ ⟧ᵉ g) d
𝔻⟦ `[] ⟧ᵉ g d = return ⊥ᶜ
𝔻⟦ t₁ `∷ t₂ ⟧ᵉ g (d₁ ∷ d₂) = 𝔻⟦ t₁ ⟧ᵉ g d₁ ⊔ᵐ 𝔻⟦ t₂ ⟧ᵉ g d₂
𝔻⟦ `foldr t₁ t₂ t₃ ⟧ᵉ g d₁₂ = do
  (g₁₂′ , d₃) ← 𝔻⟦foldr t₁ , t₂ ⟧ᵉ g (𝔼⟦ t₃ ⟧ᵉ g) d₁₂
  g₃′ ← 𝔻⟦ t₃ ⟧ᵉ g d₃
  return (g₁₂′ ⊔ᶜ g₃′)
𝔻⟦ `tick t ⟧ᵉ g d = do
  tick
  𝔻⟦ t ⟧ᵉ g d
𝔻⟦ `lazy t ⟧ᵉ g (thunk d) = 𝔻⟦ t ⟧ᵉ g d
𝔻⟦ `lazy t ⟧ᵉ g undefined = return ⊥ᶜ
𝔻⟦ `force t ⟧ᵉ g d = 𝔻⟦ t ⟧ᵉ g (thunk d)

𝔻⟦foldr t₁ , t₂ ⟧ᵉ g [] d = do
  g′ ← 𝔻⟦ t₂ ⟧ᵉ g d
  return (g′ , [])
𝔻⟦foldr t₁ , t₂ ⟧ᵉ g (x ∷ xs) d = do
  g′ ⸴ a′ ⸴ b′ ← 𝔻⟦ t₁ ⟧ᵉ (g ⸴ x ⸴ 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g xs) d
  g′′ , d′ ← 𝔻⟦foldr t₁ , t₂ ⟧′ᵉ g xs b′
  return (g′ ⊔ᶜ g′′ , a′ ∷ d′)

𝔻⟦foldr t₁ , t₂ ⟧′ᵉ g xs (thunk d) = do
  g′ , d′ ← 𝔻⟦foldr t₁ , t₂ ⟧ᵉ g xs d
  return (g′ , thunk d′)
𝔻⟦foldr t₁ , t₂ ⟧′ᵉ g xs undefined = return (⊥ᶜ , undefined)

-----------------------------
-- Order on approximations --
-----------------------------

infix 4 𝔻⟦_⟧[_≻_≤ᵉ_]
data 𝔻⟦_⟧[_≻_≤ᵉ_] : (α : Ty) (v : 𝔼⟦ α ⟧ᵗ) → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ α ⟧ᵗ≺ v → Type where
  ↓Bool : ∀ {v} → 𝔻⟦ `Bool ⟧[ v ≻ ↓Bool ≤ᵉ ↓Bool ]
  undefined : ∀ {α v d} → 𝔻⟦ `T α ⟧[ v ≻ undefined ≤ᵉ d ]
  thunk : ∀ {α v d₁ d₂} → 𝔻⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₂ ] → 𝔻⟦ `T α ⟧[ v ≻ thunk d₁ ≤ᵉ thunk d₂ ]
  [] : 𝔻⟦ `List α ⟧[ [] ≻ [] ≤ᵉ [] ]
  _∷_ : ∀ {v₁ v₂ d₁₁ d₁₂ d₂₁ d₂₂}
    → 𝔻⟦ `T α ⟧[ v₁ ≻ d₁₁ ≤ᵉ d₁₂ ]
    → 𝔻⟦ `T (`List α) ⟧[ v₂ ≻ d₂₁ ≤ᵉ d₂₂ ]
    → 𝔻⟦ `List α ⟧[ v₁ ∷ v₂ ≻ d₁₁ ∷ d₂₁ ≤ᵉ d₁₂ ∷ d₂₂ ]

-- Order on approximation contexts.
infix 4 _≤ᶜ_
_≤ᶜ_ : ∀ {Γ} {g : 𝔼⟦ Γ ⟧ᶜ} → 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ Γ ⟧ᶜ≺ g → Type
_≤ᶜ_ = AllPairwise (λ{ {α , v} → 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]})

infix 4 _≤ᵐ_
_≤ᵐ_ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Type
_≤ᵐ_ = ×.Pointwise _≤ᶜ_ ℕ._≤_

---------------------------------------------
-- (≤, ⊔, ⊥) is a bounded join-semilattice --
---------------------------------------------

⊔ᵉ-assoc : ∀ {v} → Associative _≡_ (_⊔ᵉ_ {α = α} {v = v})
⊔ᵉ-assoc ↓Bool ↓Bool ↓Bool = refl
⊔ᵉ-assoc (thunk d₁) (thunk d₂) (thunk d₃) = cong thunk (⊔ᵉ-assoc d₁ d₂ d₃)
⊔ᵉ-assoc (thunk d₁) (thunk d₂) undefined = refl
⊔ᵉ-assoc (thunk d₁) undefined (thunk d₃) = refl
⊔ᵉ-assoc (thunk d₁) undefined undefined = refl
⊔ᵉ-assoc undefined (thunk d₂) (thunk d₃) = refl
⊔ᵉ-assoc undefined (thunk d₂) undefined = refl
⊔ᵉ-assoc undefined undefined (thunk d₃) = refl
⊔ᵉ-assoc undefined undefined undefined = refl
⊔ᵉ-assoc [] [] [] = refl
⊔ᵉ-assoc (d₁ ∷ d₂) (d₃ ∷ d₄) (d₅ ∷ d₆) = cong₂ _∷_ (⊔ᵉ-assoc d₁ d₃ d₅) (⊔ᵉ-assoc d₂ d₄ d₆)

⊔ᵉ-comm : ∀ {v} → Commutative _≡_ (_⊔ᵉ_ {α = α} {v = v})
⊔ᵉ-comm ↓Bool ↓Bool = refl
⊔ᵉ-comm (thunk d₁) (thunk d₂) = cong thunk (⊔ᵉ-comm d₁ d₂)
⊔ᵉ-comm (thunk d₁) undefined = refl
⊔ᵉ-comm undefined (thunk d₂) = refl
⊔ᵉ-comm undefined undefined = refl
⊔ᵉ-comm [] [] = refl
⊔ᵉ-comm (d₁ ∷ d₂) (d₃ ∷ d₄) = cong₂ _∷_ (⊔ᵉ-comm d₁ d₃) (⊔ᵉ-comm d₂ d₄)

⊔ᵉ-idem : ∀ {v} → Idempotent _≡_ (_⊔ᵉ_ {α = α} {v = v})
⊔ᵉ-idem ↓Bool       = refl
⊔ᵉ-idem (thunk d)   = cong thunk (⊔ᵉ-idem d)
⊔ᵉ-idem undefined   = refl
⊔ᵉ-idem []          = refl
⊔ᵉ-idem (d₁₁ ∷ d₁₂) = cong₂ _∷_ (⊔ᵉ-idem d₁₁) (⊔ᵉ-idem d₁₂)

≤ᵉ-refl : ∀ {v} → Reflexive 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-refl {x = ↓Bool    } = ↓Bool
≤ᵉ-refl {x = thunk x  } = thunk ≤ᵉ-refl
≤ᵉ-refl {x = undefined} = undefined
≤ᵉ-refl {x = []       } = []
≤ᵉ-refl {x = _ ∷ _    } = ≤ᵉ-refl ∷ ≤ᵉ-refl

≤ᵉ-antisym : ∀ {v} → Antisymmetric _≡_ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-antisym ↓Bool               ↓Bool               = refl
≤ᵉ-antisym undefined           undefined           = refl
≤ᵉ-antisym (thunk d₁≤d₂)       (thunk d₂≤d₁)       = cong thunk (≤ᵉ-antisym d₁≤d₂ d₂≤d₁)
≤ᵉ-antisym []                  []                  = refl
≤ᵉ-antisym (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₁₁ ∷ d₂₂≤d₁₂) =
  cong₂ _∷_ (≤ᵉ-antisym d₁₁≤d₂₁ d₂₁≤d₁₁) (≤ᵉ-antisym d₁₂≤d₂₂ d₂₂≤d₁₂)

≤ᵉ-trans : ∀ {v} → Transitive 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-trans ↓Bool               ↓Bool               = ↓Bool
≤ᵉ-trans undefined           undefined           = undefined
≤ᵉ-trans undefined           (thunk d₂≤d₃)       = undefined
≤ᵉ-trans (thunk d₁₁≤d₂₁)     (thunk d₂₁≤d₃₁)     = thunk (≤ᵉ-trans d₁₁≤d₂₁ d₂₁≤d₃₁)
≤ᵉ-trans []                  []                  = []
≤ᵉ-trans (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) =
  ≤ᵉ-trans d₁₁≤d₂₁ d₂₁≤d₃₁ ∷ ≤ᵉ-trans d₁₂≤d₂₂ d₂₂≤d₃₂

x≤ᵉx⊔ᵉy : ∀ {v} d₁ d₂ → 𝔻⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₁ ⊔ᵉ d₂ ]
x≤ᵉx⊔ᵉy ↓Bool ↓Bool = ↓Bool
x≤ᵉx⊔ᵉy (thunk d₁₁) (thunk d₂₁) = thunk (x≤ᵉx⊔ᵉy d₁₁ d₂₁)
x≤ᵉx⊔ᵉy (thunk d₁₁) undefined   = ≤ᵉ-refl
x≤ᵉx⊔ᵉy undefined   (thunk d₂₁) = undefined
x≤ᵉx⊔ᵉy undefined   undefined   = undefined
x≤ᵉx⊔ᵉy []          []          = []
x≤ᵉx⊔ᵉy (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = x≤ᵉx⊔ᵉy d₁₁ d₂₁ ∷ x≤ᵉx⊔ᵉy d₁₂ d₂₂

x≤ᵉy⊔ᵉx : ∀ {v} d₁ d₂ → 𝔻⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₂ ⊔ᵉ d₁ ]
x≤ᵉy⊔ᵉx ↓Bool ↓Bool = ↓Bool
x≤ᵉy⊔ᵉx (thunk d₁₁) (thunk d₂₁) = thunk (x≤ᵉy⊔ᵉx d₁₁ d₂₁)
x≤ᵉy⊔ᵉx (thunk d₁₁) undefined = ≤ᵉ-refl
x≤ᵉy⊔ᵉx undefined (thunk d₂₁) = undefined
x≤ᵉy⊔ᵉx undefined undefined = undefined
x≤ᵉy⊔ᵉx [] [] = []
x≤ᵉy⊔ᵉx (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = x≤ᵉy⊔ᵉx d₁₁ d₂₁ ∷ x≤ᵉy⊔ᵉx d₁₂ d₂₂

⊔ᵉ-mono-≤ᵉ : ∀ {v} → _⊔ᵉ_ Preserves₂ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_] ⟶ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_] ⟶ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
⊔ᵉ-mono-≤ᵉ ↓Bool               ↓Bool               = ↓Bool
⊔ᵉ-mono-≤ᵉ undefined           undefined           = undefined
⊔ᵉ-mono-≤ᵉ undefined           (thunk d₂₁≤d₃₁)     = ≤ᵉ-trans (thunk d₂₁≤d₃₁) (x≤ᵉy⊔ᵉx _ _)
⊔ᵉ-mono-≤ᵉ (thunk d₁₁≤d₂₁)     undefined           = ≤ᵉ-trans (thunk d₁₁≤d₂₁) (x≤ᵉx⊔ᵉy _ _)
⊔ᵉ-mono-≤ᵉ (thunk d₁≤d₂)       (thunk d₂≤d₃)       = thunk (⊔ᵉ-mono-≤ᵉ d₁≤d₂ d₂≤d₃)
⊔ᵉ-mono-≤ᵉ []                  []                  = []
⊔ᵉ-mono-≤ᵉ (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) =
  ⊔ᵉ-mono-≤ᵉ d₁₁≤d₂₁ d₂₁≤d₃₁ ∷ ⊔ᵉ-mono-≤ᵉ d₁₂≤d₂₂ d₂₂≤d₃₂

⊔ᶜ-assoc : Associative _≡_ (_⊔ᶜ_ {g = g})
⊔ᶜ-assoc {g = []} [] [] [] = refl
⊔ᶜ-assoc {g = g ⸴ px} (g₁′ ⸴ d₁) (g₂′ ⸴ d₂) (g₃′ ⸴ d₃) = cong₂ _⸴_ (⊔ᶜ-assoc g₁′ g₂′ g₃′) (⊔ᵉ-assoc d₁ d₂ d₃)

⊔ᵐ-assoc : Associative _≡_ (_⊔ᵐ_ {g = g})
⊔ᵐ-assoc (d₁ , n₁) (d₂ , n₂) (d₃ , n₃) = ×-≡,≡→≡ (⊔ᶜ-assoc d₁ d₂ d₃ , +-assoc n₁ n₂ n₃)

⊔ᶜ-comm : Commutative _≡_ (_⊔ᶜ_ {g = g})
⊔ᶜ-comm {g = []   } []         []         = refl
⊔ᶜ-comm {g = _ ⸴ _} (g₁ ⸴ px₁) (g₂ ⸴ px₂) = cong₂ _⸴_ (⊔ᶜ-comm g₁ g₂) (⊔ᵉ-comm px₁ px₂)

⊔ᵐ-comm : Commutative _≡_ (_⊔ᵐ_ {g = g})
⊔ᵐ-comm (d₁ , n₁) (d₂ , n₂) = ×-≡,≡→≡ (⊔ᶜ-comm d₁ d₂ , +-comm n₁ n₂)

≤ᶜ-refl : {ds : 𝔻⟦ Γ ⟧ᶜ≺ g} → ds ≤ᶜ ds
≤ᶜ-refl {g = []   } {ds = []    } = []
≤ᶜ-refl {g = _ ⸴ _} {ds = ds ⸴ d} = ≤ᶜ-refl ⸴ ≤ᵉ-refl

≤ᵐ-refl : Reflexive (_≤ᵐ_ {g = g})
≤ᵐ-refl = ≤ᶜ-refl , ℕ.≤-refl

-- ≤-refl : {g : 𝔼⟦ Γ ⟧ᶜ} (m : Tick (𝔻⟦ Γ ⟧ᶜ≺ g)) → m≤ m m
-- m≤-refl = {!!}

-- m≤-⊔-mono : {g : 𝔼⟦ Γ ⟧ᶜ} (m₁ m₂ m₃ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g)) → m≤ m₁ m₂ → m≤ (m₁ ⊔ᵐ m₃) (m₂ ⊔ᵐ m₃)
-- m≤-⊔-mono m₁ m₂ m₃ p = {!!}

-- -- m≤-⊥ᵐ : {g : 𝔼⟦ Γ ⟧ᶜ} (m : Tick (↓Ctx g)) → m≤ ⊥ᵐ m
-- -- m≤-⊥ᵐ = {!!}

-- -- 𝔻⟦_⟧ᵉ-mono :
-- --   (t : Γ ⊢ τ)
-- --   (g : 𝔼⟦ Γ ⟧ᶜ) →
-- --   (d₁ d₂ : 𝔻⟦ τ ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g) →
-- --   𝔻⟦ τ ⟧[ 𝔼⟦ t ⟧ᵉ g ≻ d₁ ≤ d₂ ] →
-- --   m≤ (𝔻⟦ t ⟧ᵉ g d₁) (𝔻⟦ t ⟧ᵉ g d₂)
-- -- 𝔻⟦ ` x ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- 𝔻⟦ `let t₁ `in t₂ ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- 𝔻⟦ `false ⟧ᵉ-mono g d₁ d₂ p = m≤-refl (𝔻⟦ `false ⟧ᵉ g d₁)
-- -- 𝔻⟦ `true ⟧ᵉ-mono g d₁ d₂ p = m≤-refl (𝔻⟦ `true ⟧ᵉ g d₁)
-- -- 𝔻⟦ `if t `then t₁ `else t₂ ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- 𝔻⟦ `[] ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- 𝔻⟦ x `∷ y ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- 𝔻⟦ `foldr t t₁ t₂ ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- 𝔻⟦ `tick t ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- 𝔻⟦ `lazy t ⟧ᵉ-mono g (thunk d₁) (thunk d₂) p = {!!}
-- -- 𝔻⟦ `lazy t ⟧ᵉ-mono g undefined (thunk d₂) p = m≤-⊥ᵐ (𝔻⟦ `lazy t ⟧ᵉ g (thunk d₂))
-- -- 𝔻⟦ `lazy t ⟧ᵉ-mono g undefined undefined p = {!m≤-⊥ᵐ (𝔻⟦ `lazy t ⟧ᵉ g undefined)!}
-- -- 𝔻⟦ `force t ⟧ᵉ-mono g d₁ d₂ p = {!!}

-- data ℂ⟦_⟧ : ∀ {Γ} {g : 𝔼⟦ Γ ⟧ᶜ} (t : Γ ⊢ τ) → 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ τ ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g → ℕ → Type where
--   `false : {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} → ℂ⟦ `false ⟧ g′ ↓Bool 0
--   `true : {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} → ℂ⟦ `true ⟧ g′ ↓Bool 0
--   `if_`then : ∀ {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {t₁ t₂ t₃ m d n}  →
--     ℂ⟦ t₁ ⟧ g′ true m →
--     ℂ⟦ t₂ ⟧ g′ d n →
--     ℂ⟦ `if t₁ `then t₂ `else t₃ ⟧ g′ d (m + n)
--   `[] : ∀ {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} → ℂ⟦ `[] ⟧ g′ [] 0
--   `tick : ∀ {t₁ : Γ ⊢ τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {d c}
--     → ℂ⟦ t₁ ⟧ g′ d c
--     → ℂ⟦ t₁ ⟧ g′ d (suc c)
--   `lazy-undefined : {t₁ : Γ ⊢ τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} → ℂ⟦ `lazy t₁ ⟧ g′ undefined 0
--   `lazy-thunk : ∀ {t₁ : Γ ⊢ τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {d c}
--     → ℂ⟦ t₁ ⟧ g′ d c
--     → ℂ⟦ `lazy t₁ ⟧ g′ (thunk d) c


  -- `_               : α ∈ᴸ Γ
  --                  → Γ ⊢ α

  -- `let_`in_        : Γ ⊢ α
  --                  → Γ ⸴ α ⊢ β
  --                  → Γ ⊢ β

  -- `false           : Γ ⊢ `Bool
  -- `true            : Γ ⊢ `Bool

  -- `if_`then_`else_ : Γ ⊢ `Bool
  --                  → Γ ⊢ α
  --                  → Γ ⊢ α
  --                  → Γ ⊢ α

  -- `[]              : Γ ⊢ `List α

  -- _`∷_             : Γ ⊢ `T α
  --                  → Γ ⊢ `T (`List α)
  --                  → Γ ⊢ `List α

  -- `foldr           : Γ ⸴ `T α ⸴ `T β ⊢ β
  --                  → Γ ⊢ β
  --                  → Γ ⊢ `List α → Γ ⊢ β

  -- `tick            : Γ ⊢ α
  --                  → Γ ⊢ α

  -- `lazy            : Γ ⊢ α
  --                  → Γ ⊢ `T α

  -- `force           : Γ ⊢ `T α
  --                  → Γ ⊢ α
