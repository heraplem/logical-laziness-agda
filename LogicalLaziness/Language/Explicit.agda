module LogicalLaziness.Language.Explicit where

-- open import Algebra
-- open import Relation.Binary
-- open import Relation.Binary.PropositionalEquality
-- open import Data.Bool
--   hiding (T)
-- open import Data.Product
--   hiding (_<*>_)
-- open import Data.Product.Properties
-- open import Data.Product.Relation.Binary.Pointwise.NonDependent
--   as ×
-- open import Data.Nat
--   as ℕ
-- open import Data.Nat.Properties
--   as ℕ
-- open import Data.List
-- open import Data.List.Relation.Unary.All
--   as All

open import Data.List

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Data.List.Membership.Propositional

data Ty : Type where
  `Bool : Ty
  `T    : Ty → Ty
  `List : Ty → Ty

private
  variable
    α α₁ α₂ : Ty

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

infix 2 _⊢_
data _⊢_ : Ctx → Ty → Type where
  `_               : α ∈ᴸ Γ
                   → Γ ⊢ α

  `let_`in_        : Γ ⊢ α₁
                   → Γ ⸴ α₁ ⊢ α₂
                   → Γ ⊢ α₂

  `false           : Γ ⊢ `Bool
  `true            : Γ ⊢ `Bool

  `if_`then_`else_ : Γ ⊢ `Bool
                   → Γ ⊢ α
                   → Γ ⊢ α
                   → Γ ⊢ α

  `[]              : Γ ⊢ `List α₁

  _`∷_             : Γ ⊢ `T α₁
                   → Γ ⊢ `T (`List α₁)
                   → Γ ⊢ `List α₁

  `foldr           : Γ ⸴ `T α₁ ⸴ `T α₂ ⊢ α₂
                   → Γ ⊢ α₂
                   → Γ ⊢ `List α₁
                   → Γ ⊢ α₂

  `tick            : Γ ⊢ α
                   → Γ ⊢ α

  `lazy            : Γ ⊢ α₁
                   → Γ ⊢ `T α₁

  `force           : Γ ⊢ `T α
                   → Γ ⊢ α

-- private
--   variable
--     t : Γ ⊢ α

Tm = _⊢_

-- -- 𝔼⟦_⟧ᵗ : Ty → Type
-- -- 𝔼⟦ `Bool   ⟧ᵗ = Bool
-- -- 𝔼⟦ `T τ    ⟧ᵗ = 𝔼⟦ τ ⟧ᵗ
-- -- 𝔼⟦ `List τ ⟧ᵗ = List 𝔼⟦ τ ⟧ᵗ

-- -- 𝔼⟦_⟧ᶜ : Ctx → Type
-- -- 𝔼⟦_⟧ᶜ = All 𝔼⟦_⟧ᵗ

-- -- private
-- --   variable
-- --     g : 𝔼⟦ Γ ⟧ᶜ

-- -- ------------------------
-- -- -- Forward evaluation --
-- -- ------------------------

-- -- 𝔼⟦_⟧ᵉ : Γ ⊢ τ
-- --       → 𝔼⟦ Γ ⟧ᶜ
-- --       → 𝔼⟦ τ ⟧ᵗ

-- -- 𝔼⟦if_,_⟧ᵉ : Γ ⊢ α
-- --           → Γ ⊢ α
-- --           → 𝔼⟦ Γ ⟧ᶜ
-- --           → Bool
-- --           → 𝔼⟦ α ⟧ᵗ

-- -- 𝔼⟦foldr_,_⟧ᵉ : Γ ⸴ `T α ⸴ `T β ⊢ β
-- --              → Γ ⊢ β
-- --              → 𝔼⟦ Γ ⟧ᶜ
-- --              → List 𝔼⟦ α ⟧ᵗ
-- --              → 𝔼⟦ β ⟧ᵗ

-- -- 𝔼⟦ ` x                      ⟧ᵉ g = All.lookup g x
-- -- 𝔼⟦ `let t₁ `in t₂           ⟧ᵉ g = let a = 𝔼⟦ t₁ ⟧ᵉ g in 𝔼⟦ t₂ ⟧ᵉ (g ⸴ a)
-- -- 𝔼⟦ `false                   ⟧ᵉ g = false
-- -- 𝔼⟦ `true                    ⟧ᵉ g = true
-- -- 𝔼⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g = 𝔼⟦if t₂ , t₃ ⟧ᵉ g (𝔼⟦ t₁ ⟧ᵉ g)
-- -- 𝔼⟦ `[]                      ⟧ᵉ g = []
-- -- 𝔼⟦ t₁ `∷ t₂                 ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g ∷ 𝔼⟦ t₂ ⟧ᵉ g
-- -- 𝔼⟦ `foldr t₁ t₂ t₃          ⟧ᵉ g = 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g (𝔼⟦ t₃ ⟧ᵉ g)
-- -- 𝔼⟦ `tick t₁                 ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g
-- -- 𝔼⟦ `lazy t₁                 ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g
-- -- 𝔼⟦ `force t₁                ⟧ᵉ g = 𝔼⟦ t₁ ⟧ᵉ g

-- -- 𝔼⟦if t₁ , t₂ ⟧ᵉ g b = if b then 𝔼⟦ t₁ ⟧ᵉ g else 𝔼⟦ t₂ ⟧ᵉ g

-- -- 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g = foldr (λ a b → 𝔼⟦ t₁ ⟧ᵉ (g ⸴ a ⸴ b)) (𝔼⟦ t₂ ⟧ᵉ g)

-- -- --------------------
-- -- -- Approximations --
-- -- --------------------

-- -- infix 4 𝔻⟦_⟧ᵗ≺_ 𝔻⟦_⟧ᶜ≺_

-- -- -- `𝔻⟦ τ ⟧ᵗ≺ v` describes the set of partial values in `τ` that approximate the
-- -- -- total value `v`.
-- -- data 𝔻⟦_⟧ᵗ≺_ : (α : Ty) → 𝔼⟦ α ⟧ᵗ → Type where
-- --   false     : 𝔻⟦ `Bool ⟧ᵗ≺ false
-- --   true      : 𝔻⟦ `Bool ⟧ᵗ≺ true
-- --   thunk     : {α : Ty} {v : 𝔼⟦ α ⟧ᵗ} → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ `T α ⟧ᵗ≺ v
-- --   undefined : {α : Ty} {v : 𝔼⟦ α ⟧ᵗ} → 𝔻⟦ `T α ⟧ᵗ≺ v
-- --   []        : {α : Ty} → 𝔻⟦ `List α ⟧ᵗ≺ []
-- --   _∷_       :
-- --     ∀ {α : Ty} {v : 𝔼⟦ α ⟧ᵗ} {vs : List 𝔼⟦ α ⟧ᵗ}
-- --     → 𝔻⟦ `T α ⟧ᵗ≺ v
-- --     → 𝔻⟦ `T (`List α) ⟧ᵗ≺ vs
-- --     → 𝔻⟦ `List α ⟧ᵗ≺ v ∷ vs

-- -- -- `𝔻⟦ Γ ⟧ᶜ≺ g` is the set of evaluation contexts of shape `Γ` that elementwise
-- -- -- approximate `g`.
-- -- 𝔻⟦_⟧ᶜ≺_ : (Γ : Ctx) → 𝔼⟦ Γ ⟧ᶜ → Type
-- -- 𝔻⟦ Γ ⟧ᶜ≺ g = All (uncurry 𝔻⟦_⟧ᵗ≺_) (All.toList g)

-- -- -- `d₁ ⊔ᵉ d₂` is the least upper bound of the approximations `d₁` and `d₂`.
-- -- infixl 6 _⊔ᵉ_
-- -- _⊔ᵉ_ : {v : 𝔼⟦ α ⟧ᵗ} → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ α ⟧ᵗ≺ v
-- -- false     ⊔ᵉ false     = false
-- -- true      ⊔ᵉ true      = true
-- -- thunk x   ⊔ᵉ thunk y   = thunk (x ⊔ᵉ y)
-- -- thunk x   ⊔ᵉ undefined = thunk x
-- -- undefined ⊔ᵉ thunk y   = thunk y
-- -- undefined ⊔ᵉ undefined = undefined
-- -- []        ⊔ᵉ []        = []
-- -- (x ∷ x₁)  ⊔ᵉ (y ∷ y₁)  = x ⊔ᵉ y ∷ x₁ ⊔ᵉ y₁

-- -- -- Pairwise joins of approximation contexts.
-- -- infixl 6 _⊔ᶜ_
-- -- _⊔ᶜ_ : 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ Γ ⟧ᶜ≺ g
-- -- bs₁ ⊔ᶜ bs₂ = All.zipWith (uncurry _⊔ᵉ_) (bs₁ , bs₂)

-- -- -- Least approximation of a total value.
-- -- ⊥ᵉ : ∀ τ (v : 𝔼⟦ τ ⟧ᵗ) → 𝔻⟦ τ ⟧ᵗ≺ v
-- -- ⊥ᵉ `Bool     false   = false
-- -- ⊥ᵉ `Bool     true    = true
-- -- ⊥ᵉ (`T _)    _       = undefined
-- -- ⊥ᵉ (`List _) []      = []
-- -- ⊥ᵉ (`List _) (_ ∷ _) = undefined ∷ undefined

-- -- -- Least approximation of a total evaluation context.
-- -- ⊥ᶜ : 𝔻⟦ Γ ⟧ᶜ≺ g
-- -- ⊥ᶜ = universal (uncurry ⊥ᵉ) _

-- -- infixl 6 _⊔ᵐ_
-- -- _⊔ᵐ_ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Tick (𝔻⟦ Γ ⟧ᶜ≺ g)
-- -- m₁ ⊔ᵐ m₂ = _⊔ᶜ_ <$> m₁ <*> m₂

-- -- ⊥ᵐ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g)
-- -- ⊥ᵐ = return ⊥ᶜ

-- -- --------------------------
-- -- -- Backwards evaluation --
-- -- --------------------------

-- -- 𝔻⟦_⟧ᵉ :
-- --   (t : Γ ⊢ τ)
-- --   (g : 𝔼⟦ Γ ⟧ᶜ) →
-- --   𝔻⟦ τ ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g →
-- --   Tick (𝔻⟦ Γ ⟧ᶜ≺ g)

-- -- 𝔻⟦if_,_⟧ᵉ : ∀ {Γ α}
-- --   (t₁ t₂ : Γ ⊢ α)
-- --   (g : 𝔼⟦ Γ ⟧ᶜ)
-- --   (v : Bool) →
-- --   𝔻⟦ α ⟧ᵗ≺ 𝔼⟦if t₁ , t₂ ⟧ᵉ g v →
-- --   Tick (𝔻⟦ Γ ⟧ᶜ≺ g × 𝔻⟦ `Bool ⟧ᵗ≺ v)

-- -- 𝔻⟦foldr_,_⟧ᵉ : ∀ {Γ α β}
-- --   (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) →
-- --   (t₂ : Γ ⊢ β) →
-- --   (g : 𝔼⟦ Γ ⟧ᶜ) →
-- --   (xs : List 𝔼⟦ α ⟧ᵗ) →
-- --   𝔻⟦ β ⟧ᵗ≺ 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g xs →
-- --   Tick (𝔻⟦ Γ ⟧ᶜ≺ g × 𝔻⟦ `List α ⟧ᵗ≺ xs)

-- -- 𝔻⟦ ` x                      ⟧ᵉ g d         = return (⊥ᶜ [ ∈ᴸ⇒lookup∈ᴸtoList x ]≔ d)
-- -- 𝔻⟦ `let t₁ `in t₂           ⟧ᵉ g d₂        = do
-- --   d₁ ∷ g₂′    ← 𝔻⟦ t₂ ⟧ᵉ (g ⸴ 𝔼⟦ t₁ ⟧ᵉ g) d₂
-- --   g₁′         ← 𝔻⟦ t₁ ⟧ᵉ g d₁
-- --   return (g₁′ ⊔ᶜ g₂′)
-- -- 𝔻⟦ `false                   ⟧ᵉ g d         = return ⊥ᶜ
-- -- 𝔻⟦ `true                    ⟧ᵉ g d         = return ⊥ᶜ
-- -- 𝔻⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g d₂₃       = do
-- --   g₂₃′ , d₂   ← 𝔻⟦if t₂ , t₃ ⟧ᵉ g (𝔼⟦ t₁ ⟧ᵉ g) d₂₃
-- --   g₁′         ← 𝔻⟦ t₁ ⟧ᵉ g d₂
-- --   return (g₁′ ⊔ᶜ g₂₃′)
-- -- 𝔻⟦ `[]                      ⟧ᵉ g d         = return ⊥ᶜ
-- -- 𝔻⟦ t₁ `∷ t₂                 ⟧ᵉ g (d₁ ∷ d₂) = 𝔻⟦ t₁ ⟧ᵉ g d₁ ⊔ᵐ 𝔻⟦ t₂ ⟧ᵉ g d₂
-- -- 𝔻⟦ `foldr t₁ t₂ t₃          ⟧ᵉ g d₁₂       = do
-- --   (g₁₂′ , d₃) ← 𝔻⟦foldr t₁ , t₂ ⟧ᵉ g (𝔼⟦ t₃ ⟧ᵉ g) d₁₂
-- --   g₃′         ← 𝔻⟦ t₃ ⟧ᵉ g d₃
-- --   return (g₁₂′ ⊔ᶜ g₃′)
-- -- 𝔻⟦ `tick t                  ⟧ᵉ g d         = do
-- --   tick
-- --   𝔻⟦ t ⟧ᵉ g d
-- -- 𝔻⟦ `lazy t                  ⟧ᵉ g (thunk d) = 𝔻⟦ t ⟧ᵉ g d
-- -- 𝔻⟦ `lazy t₁                 ⟧ᵉ g undefined = return ⊥ᶜ
-- -- 𝔻⟦ `force t₁                ⟧ᵉ g d         = 𝔻⟦ t₁ ⟧ᵉ g (thunk d)

-- -- 𝔻⟦if t₂ , t₃ ⟧ᵉ g false d = do
-- --   g′ ← 𝔻⟦ t₃ ⟧ᵉ g d
-- --   return (g′ , false)
-- -- 𝔻⟦if t₂ , t₃ ⟧ᵉ g true  d = do
-- --   g′ ← 𝔻⟦ t₂ ⟧ᵉ g d
-- --   return (g′ , true)

-- -- 𝔻⟦foldr′_,_⟧ᵉ : ∀ {Γ α β}
-- --   (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) →
-- --   (t₂ : Γ ⊢ β) →
-- --   (g : 𝔼⟦ Γ ⟧ᶜ) →
-- --   (xs : List 𝔼⟦ α ⟧ᵗ) →
-- --   𝔻⟦ `T β ⟧ᵗ≺ 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g xs →
-- --   Tick (𝔻⟦ Γ ⟧ᶜ≺ g × 𝔻⟦ `T (`List α) ⟧ᵗ≺ xs)

-- -- 𝔻⟦foldr t₁ , t₂ ⟧ᵉ g []       d = do
-- --   g′           ← 𝔻⟦ t₂ ⟧ᵉ g d
-- --   return (g′ , [])
-- -- 𝔻⟦foldr t₁ , t₂ ⟧ᵉ g (x ∷ xs) d = do
-- --   g′ ⸴ a′ ⸴ b′ ← 𝔻⟦ t₁ ⟧ᵉ (g ⸴ x ⸴ 𝔼⟦foldr t₁ , t₂ ⟧ᵉ g xs) d
-- --   g′′ , d′     ← 𝔻⟦foldr′ t₁ , t₂ ⟧ᵉ g xs b′
-- --   return (g′ ⊔ᶜ g′′ , a′ ∷ d′)

-- -- 𝔻⟦foldr′ t₁ , t₂ ⟧ᵉ g xs (thunk d) = do
-- --   g′ , d′ ← 𝔻⟦foldr t₁ , t₂ ⟧ᵉ g xs d
-- --   return (g′ , thunk d′)
-- -- 𝔻⟦foldr′ t₁ , t₂ ⟧ᵉ g xs undefined = return (⊥ᶜ , undefined)

-- -- -----------------------------
-- -- -- Order on approximations --
-- -- -----------------------------

-- -- infix 4 𝔻⟦_⟧[_≻_≤ᵉ_]
-- -- data 𝔻⟦_⟧[_≻_≤ᵉ_] : (α : Ty) (v : 𝔼⟦ α ⟧ᵗ) → 𝔻⟦ α ⟧ᵗ≺ v → 𝔻⟦ α ⟧ᵗ≺ v → Type where
-- --   false : 𝔻⟦ `Bool ⟧[ false ≻ false ≤ᵉ false ]
-- --   true  : 𝔻⟦ `Bool ⟧[ true ≻ true ≤ᵉ true ]
-- --   undefined : ∀ {α v d} → 𝔻⟦ `T α ⟧[ v ≻ undefined ≤ᵉ d ]
-- --   thunk : ∀ {α v d₁ d₂} → 𝔻⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₂ ] → 𝔻⟦ `T α ⟧[ v ≻ thunk d₁ ≤ᵉ thunk d₂ ]
-- --   [] : 𝔻⟦ `List α ⟧[ [] ≻ [] ≤ᵉ [] ]
-- --   _∷_ : ∀ {v₁ v₂ d₁₁ d₁₂ d₂₁ d₂₂}
-- --     → 𝔻⟦ `T α ⟧[ v₁ ≻ d₁₁ ≤ᵉ d₁₂ ]
-- --     → 𝔻⟦ `T (`List α) ⟧[ v₂ ≻ d₂₁ ≤ᵉ d₂₂ ]
-- --     → 𝔻⟦ `List α ⟧[ v₁ ∷ v₂ ≻ d₁₁ ∷ d₂₁ ≤ᵉ d₁₂ ∷ d₂₂ ]

-- -- -- Order on approximation contexts.
-- -- infix 4 _≤ᶜ_
-- -- _≤ᶜ_ : ∀ {Γ} {g : 𝔼⟦ Γ ⟧ᶜ} → 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ Γ ⟧ᶜ≺ g → Type
-- -- _≤ᶜ_ = AllPairwise (λ{ {α , v} → 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]})

-- -- infix 4 _≤ᵐ_
-- -- _≤ᵐ_ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Tick (𝔻⟦ Γ ⟧ᶜ≺ g) → Type
-- -- _≤ᵐ_ = ×.Pointwise _≤ᶜ_ ℕ._≤_

-- -- ---------------------------------------------
-- -- -- (≤, ⊔, ⊥) is a bounded join-semilattice --
-- -- ---------------------------------------------

-- -- ⊔ᵉ-assoc : ∀ {v} → Associative _≡_ (_⊔ᵉ_ {α = α} {v = v})
-- -- ⊔ᵉ-assoc false false false = refl
-- -- ⊔ᵉ-assoc true true true = refl
-- -- ⊔ᵉ-assoc (thunk d₁) (thunk d₂) (thunk d₃) = cong thunk (⊔ᵉ-assoc d₁ d₂ d₃)
-- -- ⊔ᵉ-assoc (thunk d₁) (thunk d₂) undefined = refl
-- -- ⊔ᵉ-assoc (thunk d₁) undefined (thunk d₃) = refl
-- -- ⊔ᵉ-assoc (thunk d₁) undefined undefined = refl
-- -- ⊔ᵉ-assoc undefined (thunk d₂) (thunk d₃) = refl
-- -- ⊔ᵉ-assoc undefined (thunk d₂) undefined = refl
-- -- ⊔ᵉ-assoc undefined undefined (thunk d₃) = refl
-- -- ⊔ᵉ-assoc undefined undefined undefined = refl
-- -- ⊔ᵉ-assoc [] [] [] = refl
-- -- ⊔ᵉ-assoc (d₁ ∷ d₂) (d₃ ∷ d₄) (d₅ ∷ d₆) = cong₂ _∷_ (⊔ᵉ-assoc d₁ d₃ d₅) (⊔ᵉ-assoc d₂ d₄ d₆)

-- -- ⊔ᵉ-comm : ∀ {v} → Commutative _≡_ (_⊔ᵉ_ {α = α} {v = v})
-- -- ⊔ᵉ-comm false false = refl
-- -- ⊔ᵉ-comm true true = refl
-- -- ⊔ᵉ-comm (thunk d₁) (thunk d₂) = cong thunk (⊔ᵉ-comm d₁ d₂)
-- -- ⊔ᵉ-comm (thunk d₁) undefined = refl
-- -- ⊔ᵉ-comm undefined (thunk d₂) = refl
-- -- ⊔ᵉ-comm undefined undefined = refl
-- -- ⊔ᵉ-comm [] [] = refl
-- -- ⊔ᵉ-comm (d₁ ∷ d₂) (d₃ ∷ d₄) = cong₂ _∷_ (⊔ᵉ-comm d₁ d₃) (⊔ᵉ-comm d₂ d₄)

-- -- ⊔ᵉ-idem : ∀ {v} → Idempotent _≡_ (_⊔ᵉ_ {α = α} {v = v})
-- -- ⊔ᵉ-idem false       = refl
-- -- ⊔ᵉ-idem true       = refl
-- -- ⊔ᵉ-idem (thunk d)   = cong thunk (⊔ᵉ-idem d)
-- -- ⊔ᵉ-idem undefined   = refl
-- -- ⊔ᵉ-idem []          = refl
-- -- ⊔ᵉ-idem (d₁₁ ∷ d₁₂) = cong₂ _∷_ (⊔ᵉ-idem d₁₁) (⊔ᵉ-idem d₁₂)

-- -- ≤ᵉ-refl : ∀ {v} → Reflexive 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
-- -- ≤ᵉ-refl {x = false    } = false
-- -- ≤ᵉ-refl {x = true     } = true
-- -- ≤ᵉ-refl {x = thunk x  } = thunk ≤ᵉ-refl
-- -- ≤ᵉ-refl {x = undefined} = undefined
-- -- ≤ᵉ-refl {x = []       } = []
-- -- ≤ᵉ-refl {x = _ ∷ _    } = ≤ᵉ-refl ∷ ≤ᵉ-refl

-- -- ≤ᵉ-antisym : ∀ {v} → Antisymmetric _≡_ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
-- -- ≤ᵉ-antisym false               false               = refl
-- -- ≤ᵉ-antisym true                true                = refl
-- -- ≤ᵉ-antisym undefined           undefined           = refl
-- -- ≤ᵉ-antisym (thunk d₁≤d₂)       (thunk d₂≤d₁)       = cong thunk (≤ᵉ-antisym d₁≤d₂ d₂≤d₁)
-- -- ≤ᵉ-antisym []                  []                  = refl
-- -- ≤ᵉ-antisym (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₁₁ ∷ d₂₂≤d₁₂) =
-- --   cong₂ _∷_ (≤ᵉ-antisym d₁₁≤d₂₁ d₂₁≤d₁₁) (≤ᵉ-antisym d₁₂≤d₂₂ d₂₂≤d₁₂)

-- -- ≤ᵉ-trans : ∀ {v} → Transitive 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
-- -- ≤ᵉ-trans false               false               = false
-- -- ≤ᵉ-trans true                true                = true
-- -- ≤ᵉ-trans undefined           undefined           = undefined
-- -- ≤ᵉ-trans undefined           (thunk d₂≤d₃)       = undefined
-- -- ≤ᵉ-trans (thunk d₁₁≤d₂₁)     (thunk d₂₁≤d₃₁)     = thunk (≤ᵉ-trans d₁₁≤d₂₁ d₂₁≤d₃₁)
-- -- ≤ᵉ-trans []                  []                  = []
-- -- ≤ᵉ-trans (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) =
-- --   ≤ᵉ-trans d₁₁≤d₂₁ d₂₁≤d₃₁ ∷ ≤ᵉ-trans d₁₂≤d₂₂ d₂₂≤d₃₂

-- -- x≤ᵉx⊔ᵉy : ∀ {v} d₁ d₂ → 𝔻⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₁ ⊔ᵉ d₂ ]
-- -- x≤ᵉx⊔ᵉy false false = false
-- -- x≤ᵉx⊔ᵉy true true = true
-- -- x≤ᵉx⊔ᵉy (thunk d₁₁) (thunk d₂₁) = thunk (x≤ᵉx⊔ᵉy d₁₁ d₂₁)
-- -- x≤ᵉx⊔ᵉy (thunk d₁₁) undefined   = ≤ᵉ-refl
-- -- x≤ᵉx⊔ᵉy undefined   (thunk d₂₁) = undefined
-- -- x≤ᵉx⊔ᵉy undefined   undefined   = undefined
-- -- x≤ᵉx⊔ᵉy []          []          = []
-- -- x≤ᵉx⊔ᵉy (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = x≤ᵉx⊔ᵉy d₁₁ d₂₁ ∷ x≤ᵉx⊔ᵉy d₁₂ d₂₂

-- -- x≤ᵉy⊔ᵉx : ∀ {v} d₁ d₂ → 𝔻⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₂ ⊔ᵉ d₁ ]
-- -- x≤ᵉy⊔ᵉx false false = false
-- -- x≤ᵉy⊔ᵉx true true = true
-- -- x≤ᵉy⊔ᵉx (thunk d₁₁) (thunk d₂₁) = thunk (x≤ᵉy⊔ᵉx d₁₁ d₂₁)
-- -- x≤ᵉy⊔ᵉx (thunk d₁₁) undefined = ≤ᵉ-refl
-- -- x≤ᵉy⊔ᵉx undefined (thunk d₂₁) = undefined
-- -- x≤ᵉy⊔ᵉx undefined undefined = undefined
-- -- x≤ᵉy⊔ᵉx [] [] = []
-- -- x≤ᵉy⊔ᵉx (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = x≤ᵉy⊔ᵉx d₁₁ d₂₁ ∷ x≤ᵉy⊔ᵉx d₁₂ d₂₂

-- -- ⊔ᵉ-mono-≤ᵉ : ∀ {v} → _⊔ᵉ_ Preserves₂ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_] ⟶ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_] ⟶ 𝔻⟦ α ⟧[ v ≻_≤ᵉ_]
-- -- ⊔ᵉ-mono-≤ᵉ false               false               = false
-- -- ⊔ᵉ-mono-≤ᵉ true                true                = true
-- -- ⊔ᵉ-mono-≤ᵉ undefined           undefined           = undefined
-- -- ⊔ᵉ-mono-≤ᵉ undefined           (thunk d₂₁≤d₃₁)     = ≤ᵉ-trans (thunk d₂₁≤d₃₁) (x≤ᵉy⊔ᵉx _ _)
-- -- ⊔ᵉ-mono-≤ᵉ (thunk d₁₁≤d₂₁)     undefined           = ≤ᵉ-trans (thunk d₁₁≤d₂₁) (x≤ᵉx⊔ᵉy _ _)
-- -- ⊔ᵉ-mono-≤ᵉ (thunk d₁≤d₂)       (thunk d₂≤d₃)       = thunk (⊔ᵉ-mono-≤ᵉ d₁≤d₂ d₂≤d₃)
-- -- ⊔ᵉ-mono-≤ᵉ []                  []                  = []
-- -- ⊔ᵉ-mono-≤ᵉ (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) =
-- --   ⊔ᵉ-mono-≤ᵉ d₁₁≤d₂₁ d₂₁≤d₃₁ ∷ ⊔ᵉ-mono-≤ᵉ d₁₂≤d₂₂ d₂₂≤d₃₂

-- -- ⊔ᶜ-assoc : Associative _≡_ (_⊔ᶜ_ {g = g})
-- -- ⊔ᶜ-assoc {g = []} [] [] [] = refl
-- -- ⊔ᶜ-assoc {g = g ⸴ px} (g₁′ ⸴ d₁) (g₂′ ⸴ d₂) (g₃′ ⸴ d₃) = cong₂ _⸴_ (⊔ᶜ-assoc g₁′ g₂′ g₃′) (⊔ᵉ-assoc d₁ d₂ d₃)

-- -- ⊔ᵐ-assoc : Associative _≡_ (_⊔ᵐ_ {g = g})
-- -- ⊔ᵐ-assoc (d₁ , n₁) (d₂ , n₂) (d₃ , n₃) = ×-≡,≡→≡ (⊔ᶜ-assoc d₁ d₂ d₃ , +-assoc n₁ n₂ n₃)

-- -- ⊔ᶜ-comm : Commutative _≡_ (_⊔ᶜ_ {g = g})
-- -- ⊔ᶜ-comm {g = []   } []         []         = refl
-- -- ⊔ᶜ-comm {g = _ ⸴ _} (g₁ ⸴ px₁) (g₂ ⸴ px₂) = cong₂ _⸴_ (⊔ᶜ-comm g₁ g₂) (⊔ᵉ-comm px₁ px₂)

-- -- ⊔ᵐ-comm : Commutative _≡_ (_⊔ᵐ_ {g = g})
-- -- ⊔ᵐ-comm (d₁ , n₁) (d₂ , n₂) = ×-≡,≡→≡ (⊔ᶜ-comm d₁ d₂ , +-comm n₁ n₂)

-- -- ≤ᶜ-refl : {ds : 𝔻⟦ Γ ⟧ᶜ≺ g} → ds ≤ᶜ ds
-- -- ≤ᶜ-refl {g = []   } {ds = []    } = []
-- -- ≤ᶜ-refl {g = _ ⸴ _} {ds = ds ⸴ d} = ≤ᶜ-refl ⸴ ≤ᵉ-refl

-- -- ≤ᵐ-refl : Reflexive (_≤ᵐ_ {g = g})
-- -- ≤ᵐ-refl = ≤ᶜ-refl , ℕ.≤-refl

-- -- -- ≤-refl : {g : 𝔼⟦ Γ ⟧ᶜ} (m : Tick (𝔻⟦ Γ ⟧ᶜ≺ g)) → m≤ m m
-- -- -- m≤-refl = {!!}

-- -- -- m≤-⊔-mono : {g : 𝔼⟦ Γ ⟧ᶜ} (m₁ m₂ m₃ : Tick (𝔻⟦ Γ ⟧ᶜ≺ g)) → m≤ m₁ m₂ → m≤ (m₁ ⊔ᵐ m₃) (m₂ ⊔ᵐ m₃)
-- -- -- m≤-⊔-mono m₁ m₂ m₃ p = {!!}

-- -- -- -- m≤-⊥ᵐ : {g : 𝔼⟦ Γ ⟧ᶜ} (m : Tick (↓Ctx g)) → m≤ ⊥ᵐ m
-- -- -- -- m≤-⊥ᵐ = {!!}

-- -- -- -- 𝔻⟦_⟧ᵉ-mono :
-- -- -- --   (t : Γ ⊢ τ)
-- -- -- --   (g : 𝔼⟦ Γ ⟧ᶜ) →
-- -- -- --   (d₁ d₂ : 𝔻⟦ τ ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g) →
-- -- -- --   𝔻⟦ τ ⟧[ 𝔼⟦ t ⟧ᵉ g ≻ d₁ ≤ d₂ ] →
-- -- -- --   m≤ (𝔻⟦ t ⟧ᵉ g d₁) (𝔻⟦ t ⟧ᵉ g d₂)
-- -- -- -- 𝔻⟦ ` x ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- -- -- 𝔻⟦ `let t₁ `in t₂ ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- -- -- 𝔻⟦ `false ⟧ᵉ-mono g d₁ d₂ p = m≤-refl (𝔻⟦ `false ⟧ᵉ g d₁)
-- -- -- -- 𝔻⟦ `true ⟧ᵉ-mono g d₁ d₂ p = m≤-refl (𝔻⟦ `true ⟧ᵉ g d₁)
-- -- -- -- 𝔻⟦ `if t `then t₁ `else t₂ ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- -- -- 𝔻⟦ `[] ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- -- -- 𝔻⟦ x `∷ y ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- -- -- 𝔻⟦ `foldr t t₁ t₂ ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- -- -- 𝔻⟦ `tick t ⟧ᵉ-mono g d₁ d₂ p = {!!}
-- -- -- -- 𝔻⟦ `lazy t ⟧ᵉ-mono g (thunk d₁) (thunk d₂) p = {!!}
-- -- -- -- 𝔻⟦ `lazy t ⟧ᵉ-mono g undefined (thunk d₂) p = m≤-⊥ᵐ (𝔻⟦ `lazy t ⟧ᵉ g (thunk d₂))
-- -- -- -- 𝔻⟦ `lazy t ⟧ᵉ-mono g undefined undefined p = {!m≤-⊥ᵐ (𝔻⟦ `lazy t ⟧ᵉ g undefined)!}
-- -- -- -- 𝔻⟦ `force t ⟧ᵉ-mono g d₁ d₂ p = {!!}

-- -- open import LogicalLaziness.Base.T
-- -- open import LogicalLaziness.Base.ListA

-- -- ℂ⟦_⟧ᵗ : Ty → Type
-- -- ℂ⟦ `Bool   ⟧ᵗ = Bool
-- -- ℂ⟦ `T τ    ⟧ᵗ = T ℂ⟦ τ ⟧ᵗ
-- -- ℂ⟦ `List τ ⟧ᵗ = ListA ℂ⟦ τ ⟧ᵗ

-- -- ℂ⟦_⟧ᶜ : Ctx → Type
-- -- ℂ⟦_⟧ᶜ = All ℂ⟦_⟧ᵗ

-- -- mutual

  -- data ℂ⟦_⟧ᵉ : Γ ⊢ τ → ℂ⟦ Γ ⟧ᶜ → ℂ⟦ τ ⟧ᵗ × ℕ → Type where
  --   `_ :
  --     ∀ {g : ℂ⟦ Γ ⟧ᶜ}
  --       (x : τ ∈ᴸ Γ)
  --     → ℂ⟦ ` x ⟧ᵉ g ∋ (All.lookup g x , 0)
  --   `let_`in_ :
  --     ∀ {g : ℂ⟦ Γ ⟧ᶜ} {t₁ : Γ ⊢ α} {t₂ : Γ ⸴ α ⊢ β} {a b c₁ c₂}
  --     → ℂ⟦ t₁ ⟧ᵉ g ∋ (a , c₁)
  --     → ℂ⟦ t₂ ⟧ᵉ (g ⸴ a) ∋ (b , c₂)
  --     → ℂ⟦ `let t₁ `in t₂ ⟧ᵉ g ∋ (b , c₁ + c₂)
  --   `false :
  --     ∀ {g : ℂ⟦ Γ ⟧ᶜ}
  --     → ℂ⟦ `false ⟧ᵉ g ∋ (false , 0)
  --   `true :
  --     ∀ {g : ℂ⟦ Γ ⟧ᶜ}
  --     → ℂ⟦ `true ⟧ᵉ g ∋ (true , 0)
  --   `if_`else_ :
  --     ∀ {g : ℂ⟦ Γ ⟧ᶜ} {t₁} {t₂ t₃ : Γ ⊢ τ} {v c₁ c₂}
  --     → ℂ⟦ t₁ ⟧ᵉ g (false , c₁)
  --     → ℂ⟦ t₃ ⟧ᵉ g (v , c₂)
  --     → ℂ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g (v , c₁ + c₂)
  --   `if_`then_ :
  --     ∀ {g : ℂ⟦ Γ ⟧ᶜ} {t₁} {t₂ t₃ : Γ ⊢ τ} {v c₁ c₂}
  --     → ℂ⟦ t₁ ⟧ᵉ g (true , c₁)
  --     → ℂ⟦ t₂ ⟧ᵉ g (v , c₂)
  --     → ℂ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g (v , c₁ + c₂)
  --   `[] :
  --     ∀ {g : ℂ⟦ Γ ⟧ᶜ}
  --     → ℂ⟦ `[] ∶ Γ ⊢ `List τ ⟧ᵉ g ∋ ([] , 0)
  --   _`∷_ :
  --     ∀ {t₁ : Γ ⊢ `T τ} {t₂ : Γ ⊢ `T (`List τ)} {g : ℂ⟦ Γ ⟧ᶜ} {a₁ a₂ c₁ c₂}
  --     → ℂ⟦ t₁ ⟧ᵉ g ∋ (a₁ , c₁)
  --     → ℂ⟦ t₂ ⟧ᵉ g ∋ (a₂ , c₂)
  --     → ℂ⟦ t₁ `∷ t₂ ⟧ᵉ g ∋ (a₁ ∷ a₂ , c₁ + c₂)
  --   `foldr :
  --     ∀ {t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β} {t₂ : Γ ⊢ β} {t₃ : Γ ⊢ `List α}
  --       {g : ℂ⟦ Γ ⟧ᶜ} {as b c₁ c₂}
  --     → ℂ⟦foldr t₁ , t₂ ⟧ᵉ g as ∋ (b , c₂)
  --     → ℂ⟦ t₃ ⟧ᵉ g ∋ (as , c₁)
  --     → ℂ⟦ `foldr t₁ t₂ t₃ ⟧ᵉ g ∋ (b , c₁ + c₂)
  --   `tick :
  --     ∀ {t₁ : Γ ⊢ τ} {g : ℂ⟦ Γ ⟧ᶜ} {a c}
  --     → ℂ⟦ t₁ ⟧ᵉ g ∋ (a , c)
  --     → ℂ⟦ `tick t₁ ⟧ᵉ g ∋ (a , suc c)
  --   `lazy-undefined :
  --     ∀ {t₁ : Γ ⊢ τ} {g : ℂ⟦ Γ ⟧ᶜ}
  --     → ℂ⟦ `lazy t₁ ⟧ᵉ g ∋ (undefined , 0)
  --   `lazy-thunk :
  --     ∀ {t₁ : Γ ⊢ τ} {g : ℂ⟦ Γ ⟧ᶜ} {a c}
  --     → ℂ⟦ t₁ ⟧ᵉ g ∋ (a , c)
  --     → ℂ⟦ `lazy t₁ ⟧ᵉ g ∋ (thunk a , c)
  --   `force :
  --     ∀ {t₁ : Γ ⊢ `T τ} {g : ℂ⟦ Γ ⟧ᶜ} {a c}
  --     → ℂ⟦ t₁ ⟧ᵉ g ∋ (thunk a , c)
  --     → ℂ⟦ `force t₁ ⟧ᵉ g ∋ (a , c)

  -- data ℂ⟦foldr_,_⟧ᵉ (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) (t₂ : Γ ⊢ β) : ℂ⟦ Γ ⟧ᶜ → ListA ℂ⟦ α ⟧ᵗ → ℂ⟦ β ⟧ᵗ × ℕ → Type where
  --   `foldr-[] :
  --     ∀ {g b c}
  --     → ℂ⟦ t₂ ⟧ᵉ g ∋ (b , c)
  --     → ℂ⟦foldr t₁ , t₂ ⟧ᵉ g [] ∋ (b , c)
  --   `foldr-∷ :
  --     ∀ {g a as b b′ c₁ c₂}
  --     → ℂ⟦ t₁ ⟧ᵉ (g ⸴ a ⸴ b) ∋ (b′ , c₁)
  --     → ℂ⟦foldr′ t₁ , t₂ ⟧ᵉ g as ∋ (b , c₂)
  --     → ℂ⟦foldr t₁ , t₂ ⟧ᵉ g (a ∷ as) ∋ (b′ , c₁ + c₂)

--   data ℂ⟦foldr′_,_⟧ᵉ (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) (t₂ : Γ ⊢ β) : ℂ⟦ Γ ⟧ᶜ → T (ListA ℂ⟦ α ⟧ᵗ) → T ℂ⟦ β ⟧ᵗ × ℕ → Type where
--     `foldr′-undefined :
--       ∀ {g}
--       → ℂ⟦foldr′ t₁ , t₂ ⟧ᵉ g undefined ∋ (undefined , 0)
--     `foldr′-thunk :
--       ∀ {g as b c}
--       → ℂ⟦foldr t₁ , t₂ ⟧ᵉ g as ∋ (b , c)
--       → ℂ⟦foldr′ t₁ , t₂ ⟧ᵉ g (thunk as) ∋ (thunk b , c)

-- -- infix 4 ℂ⟦_⟧ᵗ[_≤ᵉ_]
-- -- data ℂ⟦_⟧ᵗ[_≤ᵉ_] : (α : Ty) → ℂ⟦ α ⟧ᵗ → ℂ⟦ α ⟧ᵗ → Type where
-- --   false : ℂ⟦ `Bool ⟧ᵗ[ false ≤ᵉ false ]
-- --   true  : ℂ⟦ `Bool ⟧ᵗ[ true ≤ᵉ true ]
-- --   undefined : ∀ {α d} → ℂ⟦ `T α ⟧ᵗ[ undefined ≤ᵉ d ]
-- --   thunk : ∀ {α d₁ d₂} → ℂ⟦ α ⟧ᵗ[ d₁ ≤ᵉ d₂ ] → ℂ⟦ `T α ⟧ᵗ[ thunk d₁ ≤ᵉ thunk d₂ ]
-- --   [] : ℂ⟦ `List α ⟧ᵗ[ [] ≤ᵉ [] ]
-- --   _∷_ : ∀ {d₁₁ d₁₂ d₂₁ d₂₂}
-- --     → ℂ⟦ `T α ⟧ᵗ[ d₁₁ ≤ᵉ d₁₂ ]
-- --     → ℂ⟦ `T (`List α) ⟧ᵗ[ d₂₁ ≤ᵉ d₂₂ ]
-- --     → ℂ⟦ `List α ⟧ᵗ[ d₁₁ ∷ d₂₁ ≤ᵉ d₁₂ ∷ d₂₂ ]

-- -- infix 4 ℂ⟦_⟧[_≤ᶜ_]
-- -- ℂ⟦_⟧[_≤ᶜ_] : (Γ : Ctx) → ℂ⟦ Γ ⟧ᶜ → ℂ⟦ Γ ⟧ᶜ → Type
-- -- ℂ⟦ Γ ⟧[ g₁ ≤ᶜ g₂ ] = AllPairwise ℂ⟦ _ ⟧ᵗ[_≤ᵉ_] g₁ g₂

-- -- ℂ-mono : ∀ {t : Γ ⊢ α} {g₁ g₂ : ℂ⟦ Γ ⟧ᶜ} {m} → ℂ⟦_⟧[_≤ᶜ_] Γ g₁ g₂ → ℂ⟦ t ⟧ᵉ g₁ ∋ m → ℂ⟦ t ⟧ᵉ g₂ ∋ m
-- -- ℂ-mono p (` x) = {!!}
-- -- ℂ-mono p (`let δ₁ `in δ₂) = `let ℂ-mono p δ₁ `in ℂ-mono (p ⸴ {!!}) δ₂
-- -- ℂ-mono p `false = `false
-- -- ℂ-mono p `true = `true
-- -- ℂ-mono p (`if q `else q₁) = `if ℂ-mono p q `else ℂ-mono p q₁
-- -- ℂ-mono p (`if q `then q₁) = `if ℂ-mono p q `then ℂ-mono p q₁
-- -- ℂ-mono p `[] = `[]
-- -- ℂ-mono p (δ₁ `∷ δ₂) = ℂ-mono p δ₁ `∷ ℂ-mono p δ₂
-- -- ℂ-mono p (`foldr x x₁) = {!!}
-- -- ℂ-mono p (`tick δ₁) = `tick (ℂ-mono p δ₁)
-- -- ℂ-mono p `lazy-undefined = `lazy-undefined
-- -- ℂ-mono p (`lazy-thunk δ₁) = `lazy-thunk (ℂ-mono p δ₁)
-- -- ℂ-mono p (`force δ₁) = `force (ℂ-mono p δ₁)

-- -- ℂ⌊_⌋ᵉ : ∀ {α v} → 𝔻⟦ α ⟧ᵗ≺ v → ℂ⟦ α ⟧ᵗ
-- -- ℂ⌊_⌋ᵉ {α = `Bool} false = false
-- -- ℂ⌊_⌋ᵉ {α = `Bool} true  = true
-- -- ℂ⌊_⌋ᵉ {α = `T α} undefined = undefined
-- -- ℂ⌊_⌋ᵉ {α = `T α} (thunk d) = thunk ℂ⌊ d ⌋ᵉ
-- -- ℂ⌊_⌋ᵉ {α = `List α} [] = []
-- -- ℂ⌊_⌋ᵉ {α = `List α} (d₁ ∷ d₂) = ℂ⌊ d₁ ⌋ᵉ ∷ ℂ⌊ d₂ ⌋ᵉ

-- -- ℂ⌊_⌋ᶜ : 𝔻⟦ Γ ⟧ᶜ≺ g → ℂ⟦ Γ ⟧ᶜ
-- -- ℂ⌊_⌋ᶜ {g = []} [] = []
-- -- ℂ⌊_⌋ᶜ {g = g ⸴ v} (g′ ⸴ d) = ℂ⌊ g′ ⌋ᶜ ⸴ ℂ⌊ d ⌋ᵉ

-- -- open import Function
-- --   using ( case_of_
-- --         ; case_returning_of_
-- --         )
-- -- import Effect.Applicative
-- -- import Effect.Monad


-- -- 𝔻⊆ℂ :
-- --   ∀ {Γ α}
-- --     (t : Γ ⊢ α)
-- --     (g : 𝔼⟦ Γ ⟧ᶜ)
-- --     (outD : 𝔻⟦ α ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g) →
-- --     let (inDs , c) = 𝔻⟦ t ⟧ᵉ g outD
-- --     in ℂ⟦ t ⟧ᵉ ℂ⌊ inDs ⌋ᶜ ∋ (ℂ⌊ outD ⌋ᵉ , c)

-- -- -- lemma-if :
-- -- --   ∀ {Γ α}
-- -- --     (t₁ : Γ ⊢ `Bool) (t₂ t₃ : Γ ⊢ α)
-- -- --     (g : 𝔼⟦ Γ ⟧ᶜ)
-- -- --     (b : Bool)
-- -- --   → b ≡ 𝔼⟦ t₁ ⟧ᵉ g
-- -- --   → (outD : 𝔻⟦ α ⟧ᵗ≺ 𝔼⟦if t₂ , t₃ ⟧ᵉ g b)
-- -- --   → ℂ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ ℂ⌊ (λ { (g₂₃′ , d₂)
-- -- --        → (rawMonad-Tick Effect.Monad.RawMonad.>>= 𝔻⟦ t₁ ⟧ᵉ g d₂)
-- -- --          (λ g₁′ →
-- -- --             Effect.Applicative.RawApplicative.return
-- -- --             (Effect.Monad.RawMonad.rawApplicative rawMonad-Tick) (g₁′ ⊔ᶜ g₂₃′))
-- -- --     })
-- -- --   (𝔻⟦if t₂ , t₃ ⟧ᵉ g b outD .proj₁) .proj₁
-- -- --   ⌋ᶜ ∋ (ℂ⌊ outD ⌋ᵉ ,
-- -- --    𝔻⟦if t₂ , t₃ ⟧ᵉ g b outD .proj₂ +
-- -- --    (λ { (g₂₃′ , d₂)
-- -- --           → (rawMonad-Tick Effect.Monad.RawMonad.>>= 𝔻⟦ t₁ ⟧ᵉ g d₂)
-- -- --             (λ g₁′ → Effect.Monad.RawMonad.return rawMonad-Tick (g₁′ ⊔ᶜ g₂₃′))
-- -- --       })
-- -- --    (𝔻⟦if t₂ , t₃ ⟧ᵉ g b outD .proj₁) .proj₂)
-- -- -- lemma-if t₁ t₂ t₃ g false eqn outD = `if {!lemma t₁ g !} `else 𝔻⊆ℂ t₃ g outD
-- -- -- lemma-if t₁ t₂ t₃ g true eqn outD = {!!}


-- -- 𝔻⊆ℂ (` x) g outD = {!outD!}
-- -- 𝔻⊆ℂ (`let t₁ `in t₂) g outD = {!!}
-- -- 𝔻⊆ℂ `false g false = `false
-- -- 𝔻⊆ℂ `true g true = `true
-- -- 𝔻⊆ℂ (`if t₁ `then t₂ `else t₃) g = {!!}
-- -- -- case (𝔼⟦ t₁ ⟧ᵉ g , inspect 𝔼⟦ t₁ ⟧ᵉ g) of λ{
-- -- --   (false , [ eqn ]) → {!!} ;
-- -- --   (true , [ eqn ]) → {!!}
-- -- --   }

-- -- -- = {!!}
-- -- 𝔻⊆ℂ `[] g [] = `[]
-- -- 𝔻⊆ℂ (t₁ `∷ t₂) g (outD₁ ∷ outD₂) = {!𝔻⊆ℂ t₁ g outD₁!}
-- -- 𝔻⊆ℂ (`foldr t₁ t₂ t₃) g outD = {!!}
-- -- 𝔻⊆ℂ (`tick t₁) g outD = `tick (𝔻⊆ℂ t₁ g outD)
-- -- 𝔻⊆ℂ (`lazy t₁) g (thunk outD₁) = `lazy-thunk (𝔻⊆ℂ t₁ g outD₁)
-- -- 𝔻⊆ℂ (`lazy t₁) g undefined = `lazy-undefined
-- -- 𝔻⊆ℂ (`force t₁) g outD = `force (𝔻⊆ℂ t₁ g (thunk outD))

-- -- -- ℂ⊆𝔻 :
-- -- --   {g : 𝔼⟦ Γ ⟧ᶜ}
-- -- --   (a : 𝔼⟦ α ⟧ᵗ)
-- -- --   (t : Γ ⸴ α ⊢ β)
-- -- --   (outD : 𝔻⟦ β ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ (g ⸴ a)) →
-- -- --   case 𝔻⟦ t ⟧ᵉ (g ⸴ a) outD of λ{
-- -- --     ((inDs ⸴ inD) , c) → ⟦ demand₂ t a ⟧ᵉ (Ctx⟦ inDs ⟧ₑ ⸴ ⟦ outD ⟧ᵉₐ) ∋ (⟦ inD ⟧ᵉₐ , c)
-- -- --   }

-- -- -- data ℂ⟦_⟧ : ∀ {Γ} (t : Γ ⊢ τ) {g : 𝔼⟦ Γ ⟧ᶜ} → 𝔻⟦ Γ ⟧ᶜ≺ g → 𝔻⟦ τ ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g × ℕ → Type where
-- -- --   `_ :
-- -- --     ∀ {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {x : τ ∈ᴸ Γ}
-- -- --     → ℂ⟦ ` x ⟧ g′ ∋ (All.lookup g′ (∈ᴸ⇒lookup∈ᴸtoList x) , 0)
-- -- --   `let_`in_ :
-- -- --     ∀ {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {t₁ : Γ ⊢ α} {t₂ : Γ ⸴ α ⊢ β} {d₁ d₂ c₁ c₂}
-- -- --     → ℂ⟦ t₁ ⟧ g′ ∋ (d₁ , c₁)
-- -- --     → ℂ⟦ t₂ ⟧ (g′ ⸴ d₁) ∋ (d₂ , c₂)
-- -- --     → ℂ⟦ `let t₁ `in t₂ ⟧ g′ ∋ (d₂ , c₁ + c₂)
-- -- --   `false :
-- -- --     ∀ {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g}
-- -- --     → ℂ⟦ `false ⟧ g′ ∋ (false , 0)
-- -- --   `true :
-- -- --     ∀ {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g}
-- -- --     → ℂ⟦ `true ⟧ g′ ∋ (true , 0)
-- -- --   `if_`then :
-- -- --     ∀ {t₁ : Γ ⊢ `Bool} {t₂ t₃ : Γ ⊢ τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {d₁ d₂ m n}
-- -- --     → ℂ⟦ t₁ ⟧ g′ (d₁ , m)
-- -- --     → ℂ⟦ if 𝔼⟦ t₁ ⟧ᵉ g then t₂ else t₃ ⟧ g′ (d₂ , n)
-- -- --     → ℂ⟦ `if t₁ `then t₂ `else t₃ ⟧ g′ ∋ (d₂ , m + n)
-- -- --   `[] : ∀ {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} → ℂ⟦ `[] ⟧ g′ ∋ ([] , 0)
-- -- --   _`∷_ :
-- -- --     ∀ {t₁ : Γ ⊢ `T τ} {t₂ : Γ ⊢ `T (`List τ)} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {d₁ d₂ c₁ c₂}
-- -- --     → ℂ⟦ t₁ ⟧ g′ ∋ (d₁ , c₁)
-- -- --     → ℂ⟦ t₂ ⟧ g′ ∋ (d₂ , c₂)
-- -- --     → ℂ⟦ t₁ `∷ t₂ ⟧ g′ ∋ (d₁ ∷ d₂ , c₁ + c₂)
-- -- --   `tick :
-- -- --     ∀ {t₁ : Γ ⊢ τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {d c}
-- -- --     → ℂ⟦ t₁ ⟧ g′ ∋ (d , c)
-- -- --     → ℂ⟦ t₁ ⟧ g′ ∋ (d , suc c)
-- -- --   `lazy-undefined :
-- -- --     ∀ {t₁ : Γ ⊢ τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g}
-- -- --     → ℂ⟦ `lazy t₁ ⟧ g′ ∋ (undefined , 0)
-- -- --   `lazy-thunk :
-- -- --     ∀ {t₁ : Γ ⊢ τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {d c}
-- -- --     → ℂ⟦ t₁ ⟧ g′ ∋ (d , c)
-- -- --     → ℂ⟦ `lazy t₁ ⟧ g′ ∋ (thunk d , c)
-- -- --   `force :
-- -- --     ∀ {t₁ : Γ ⊢ `T τ} {g′ : 𝔻⟦ Γ ⟧ᶜ≺ g} {d c}
-- -- --     → ℂ⟦ t₁ ⟧ g′ ∋ (thunk d , c)
-- -- --     → ℂ⟦ `force t₁ ⟧ g′ ∋ (d , c)


-- --   -- `_               : α ∈ᴸ Γ
-- --   --                  → Γ ⊢ α

-- --   -- `let_`in_        : Γ ⊢ α
-- --   --                  → Γ ⸴ α ⊢ β
-- --   --                  → Γ ⊢ β

-- --   -- `false           : Γ ⊢ `Bool
-- --   -- `true            : Γ ⊢ `Bool

-- --   -- `if_`then_`else_ : Γ ⊢ `Bool
-- --   --                  → Γ ⊢ α
-- --   --                  → Γ ⊢ α
-- --   --                  → Γ ⊢ α

-- --   -- `[]              : Γ ⊢ `List α

-- --   -- _`∷_             : Γ ⊢ `T α
-- --   --                  → Γ ⊢ `T (`List α)
-- --   --                  → Γ ⊢ `List α

-- --   -- `foldr           : Γ ⸴ `T α ⸴ `T β ⊢ β
-- --   --                  → Γ ⊢ β
-- --   --                  → Γ ⊢ `List α → Γ ⊢ β

-- --   -- `tick            : Γ ⊢ α
-- --   --                  → Γ ⊢ α

-- --   -- `lazy            : Γ ⊢ α
-- --   --                  → Γ ⊢ `T α

-- --   -- `force           : Γ ⊢ `T α
-- --   --                  → Γ ⊢ α
