module LogicalLaziness.Language.Explicit.Semantics.Demand where

open import Function
open import Relation.Binary
open import Relation.Binary.Lattice
import Relation.Binary.Lattice.Properties.JoinSemilattice
open import Relation.Binary.PropositionalEquality
  as ≡
open import Algebra
open import Data.Bool
  hiding (_≤_)
open import Data.Product
  as ×
open import Data.Product.Properties
open import Data.Nat
  as ℕ
  hiding (_≤_; _⊔_)
open import Data.Nat.Properties
  as ℕ
open import Data.List
open import Data.List.Relation.Unary.All
  as All
import Data.List.Relation.Binary.Pointwise
  as List
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  as ×

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Effect.Monad.Tick
import LogicalLaziness.Base.Data.Product.Relation.Binary.Pointwise
  as ×
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Base.Data.List.All
  as All
open import LogicalLaziness.Base.Data.List.All.Relation.Binary.Pointwise
  as AllPointwise
  using ( []
        ; _∷_
        )
  renaming (Pointwise to AllPointwise)
open import LogicalLaziness.Language.Explicit
open import LogicalLaziness.Language.Explicit.Semantics.Eval
  as 𝔼
  hiding ( ⟦_⟧ᵉ
         ; ⟦if_,_⟧ᵉ
         ; ⟦foldr_,_⟧ᵉ
         )

private
  variable
    Γ Γ₁ Γ₂ : Ctx
    α α₁ α₂ β : Ty
    γ : 𝔼.⟦ Γ ⟧ᶜ
    γ₁ : 𝔼.⟦ Γ₁ ⟧ᶜ
    γ₂ : 𝔼.⟦ Γ₂ ⟧ᶜ

---------------------------------------------
-- The bounded join-semilattice of demands --
---------------------------------------------

-- `⟦ α ⟧≺ᵗ v` describes the set of demands in `α` that approximate the total
-- value `v`.
infix 4 ⟦_⟧≺ᵗ_
data ⟦_⟧≺ᵗ_ : (α : Ty) → 𝔼.⟦ α ⟧ᵗ → Type where
  false     : ⟦ `Bool ⟧≺ᵗ false
  true      : ⟦ `Bool ⟧≺ᵗ true
  thunk     : {v : 𝔼.⟦ α ⟧ᵗ}
            → ⟦ α ⟧≺ᵗ v
            → ⟦ `T α ⟧≺ᵗ v
  undefined : {v : 𝔼.⟦ α ⟧ᵗ}
            → ⟦ `T α ⟧≺ᵗ v
  []        : ⟦ `List α ⟧≺ᵗ []
  _∷_       : {v : 𝔼.⟦ α ⟧ᵗ} {vs : List 𝔼.⟦ α ⟧ᵗ}
            → ⟦ α ⟧≺ᵗ v
            → ⟦ `T (`List α) ⟧≺ᵗ vs
            → ⟦ `List α ⟧≺ᵗ v ∷ vs

-- Now we introduce a join-semilattice (≤, ⊔, ⊥) of demands (on a fixed value).
-- We do not prove any properties yet.

infix 4 ⟦_⟧[_≻_≤ᵗ_]
data ⟦_⟧[_≻_≤ᵗ_] : (α : Ty) (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧≺ᵗ v → ⟦ α ⟧≺ᵗ v → Type where
  false     : ⟦ `Bool ⟧[ false ≻ false ≤ᵗ false ]
  true      : ⟦ `Bool ⟧[ true  ≻ true  ≤ᵗ true  ]
  undefined : ∀ {v d}
            → ⟦ `T α ⟧[ v ≻ undefined ≤ᵗ d ]
  thunk     : ∀ {v d₁ d₂}
            → ⟦ α ⟧[ v ≻ d₁ ≤ᵗ d₂ ]
            → ⟦ `T α ⟧[ v ≻ thunk d₁ ≤ᵗ thunk d₂ ]
  []        : ⟦ `List α ⟧[ [] ≻ [] ≤ᵗ [] ]
  _∷_       : ∀ {v₁ v₂ d₁₁ d₁₂ d₂₁ d₂₂}
            → ⟦ α ⟧[ v₁ ≻ d₁₁ ≤ᵗ d₁₂ ]
            → ⟦ `T (`List α) ⟧[ v₂ ≻ d₂₁ ≤ᵗ d₂₂ ]
            → ⟦ `List α ⟧[ v₁ ∷ v₂ ≻ d₁₁ ∷ d₂₁ ≤ᵗ d₁₂ ∷ d₂₂ ]

infix 4 _≤ᵗ_
_≤ᵗ_ : {α : Ty} {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧≺ᵗ v → ⟦ α ⟧≺ᵗ v → Type
_≤ᵗ_ = ⟦ _ ⟧[ _ ≻_≤ᵗ_]

-- `d₁ ⊔ᵗ d₂` is the join of the demands `d₁` and `d₂`.
infixl 6 _⊔ᵗ_
_⊔ᵗ_ : {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧≺ᵗ v → ⟦ α ⟧≺ᵗ v → ⟦ α ⟧≺ᵗ v
false       ⊔ᵗ false       = false
true        ⊔ᵗ true        = true
thunk d₁    ⊔ᵗ thunk d₂    = thunk (d₁ ⊔ᵗ d₂)
thunk d₁    ⊔ᵗ undefined   = thunk d₁
undefined   ⊔ᵗ thunk d₂    = thunk d₂
undefined   ⊔ᵗ undefined   = undefined
[]          ⊔ᵗ []          = []
(d₁₁ ∷ d₁₂) ⊔ᵗ (d₂₁ ∷ d₂₂) = d₁₁ ⊔ᵗ d₂₁ ∷ d₁₂ ⊔ᵗ d₂₂

-- `⊥⟦ α ⟧≺ᵗ v` is the least demand in `α` on the total value `v`.
infix 4 ⊥⟦_⟧≺ᵗ_
⊥⟦_⟧≺ᵗ_ : ∀ α (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧≺ᵗ v
⊥⟦ `Bool   ⟧≺ᵗ false   = false
⊥⟦ `Bool   ⟧≺ᵗ true     = true
⊥⟦ `T α    ⟧≺ᵗ v        = undefined
⊥⟦ `List α ⟧≺ᵗ []       = []
⊥⟦ `List α ⟧≺ᵗ (v ∷ vs) = (⊥⟦ α ⟧≺ᵗ v) ∷ undefined

⊥ᵗ : ∀ {α} {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧≺ᵗ v
⊥ᵗ = ⊥⟦ _ ⟧≺ᵗ _

-----------------------------------------------------
-- The bounded join-semilattice of demand contexts --
-----------------------------------------------------

-- A demand context on an evaluation context `γ` (itself over a typing context
-- `Γ`) assigns to each value `v` in `γ` some demand on `v`.

infix 4 ⟦_⟧≺ᶜ_
⟦_⟧≺ᶜ_ : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → Type
⟦ Γ ⟧≺ᶜ γ = All (uncurry ⟦_⟧≺ᵗ_) (All.toList γ)

infix 4 ≺ᶜ_
≺ᶜ_ : 𝔼.⟦ Γ ⟧ᶜ → Type
≺ᶜ γ = All (uncurry ⟦_⟧≺ᵗ_) (All.toList γ)

private
  variable
    δ δ₁ δ₂ δ₃ : ≺ᶜ γ

-- The bounded join-semilattice of demands can be extended pointwise to a
-- bounded join-semilattice of demand contexts.

infix 4 ⟦_⟧[_≻_≤ᶜ_]
⟦_⟧[_≻_≤ᶜ_] : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → ≺ᶜ γ → ≺ᶜ γ → Type
⟦ Γ ⟧[ γ ≻ δ₁ ≤ᶜ δ₂ ] = AllPointwise _≤ᵗ_ δ₁ δ₂

infix 4 _≤ᶜ_
_≤ᶜ_ : ≺ᶜ γ → ≺ᶜ γ → Type
δ₁ ≤ᶜ δ₂ = ⟦ _ ⟧[ _ ≻ δ₁ ≤ᶜ δ₂ ]

infixl 6 _⊔ᶜ_
_⊔ᶜ_ : ≺ᶜ γ → ≺ᶜ γ → ≺ᶜ γ
δ₁ ⊔ᶜ δ₂ = All.zipWith (uncurry _⊔ᵗ_) (δ₁ , δ₂)

-- `⊥⟦ Γ ⟧≺ᶜ γ` is the least demand context of shape `Γ` on the evaluation
-- context `γ`.
infix 4 ⊥⟦_⟧≺ᶜ_
⊥⟦_⟧≺ᶜ_ : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → ⟦ Γ ⟧≺ᶜ γ
⊥⟦ Γ ⟧≺ᶜ γ = All.universal (λ _ → ⊥ᵗ) (All.toList γ)

⊥ᶜ : ≺ᶜ γ
⊥ᶜ = ⊥⟦ _ ⟧≺ᶜ _

---------------------------------------------------------
-- The bounded join-semilattice of contexts with costs --
---------------------------------------------------------

infix 4 ⟦_⟧≺ᵐ_
⟦_⟧≺ᵐ_ : (Γ : Ctx) → 𝔼.⟦ Γ ⟧ᶜ → Type
⟦ Γ ⟧≺ᵐ γ = Tick (⟦ Γ ⟧≺ᶜ γ)

infix 4 ≺ᵐ_
≺ᵐ_ : 𝔼.⟦ Γ ⟧ᶜ → Type
≺ᵐ γ = ⟦ _ ⟧≺ᵐ γ

infix 4 ⟦_⟧[_≻_≤ᵐ_]
⟦_⟧[_≻_≤ᵐ_] : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → ⟦ Γ ⟧≺ᵐ γ → ⟦ Γ ⟧≺ᵐ γ → Type
⟦ Γ ⟧[ γ ≻ m₁ ≤ᵐ m₂ ] = Pointwise _≤ᶜ_ ℕ._≤_ m₁ m₂

infix 4 _≤ᵐ_
_≤ᵐ_ : ≺ᵐ γ → ≺ᵐ γ → Type
_≤ᵐ_ = ⟦ _ ⟧[ _ ≻_≤ᵐ_]

infixl 6 _⊔ᵐ_
_⊔ᵐ_ : ≺ᵐ γ → ≺ᵐ γ → ≺ᵐ γ
_⊔ᵐ_ = ×.zip _⊔ᶜ_ _+_

infix 4 ⊥⟦_⟧≺ᵐ_
⊥⟦_⟧≺ᵐ_ : ∀ Γ (γ : 𝔼.⟦ Γ ⟧ᶜ) → ⟦ Γ ⟧≺ᵐ γ
⊥⟦ Γ ⟧≺ᵐ γ = return (⊥⟦ Γ ⟧≺ᶜ γ)

⊥ᵐ : ≺ᵐ γ
⊥ᵐ = ⊥⟦ _ ⟧≺ᵐ _

-- Convert from evaluation semantics values

𝔼⟦_⟧[_]ᵗ : (α : Ty) (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧≺ᵗ v
𝔼⟦ `Bool   ⟧[ false  ]ᵗ = false
𝔼⟦ `Bool   ⟧[ true   ]ᵗ = true
𝔼⟦ `T α    ⟧[ x      ]ᵗ = thunk 𝔼⟦ α ⟧[ x ]ᵗ
𝔼⟦ `List α ⟧[ []     ]ᵗ = []
𝔼⟦ `List α ⟧[ x ∷ xs ]ᵗ = 𝔼⟦ α ⟧[ x ]ᵗ ∷ 𝔼⟦ `T (`List α) ⟧[ xs ]ᵗ

𝔼[_]ᵗ : (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧≺ᵗ v
𝔼[_]ᵗ = 𝔼⟦ _ ⟧[_]ᵗ

𝔼⟦_⟧[_]ᶜ : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → ⟦ Γ ⟧≺ᶜ γ
𝔼⟦ _ ⟧[ γ ]ᶜ = universal (uncurry 𝔼⟦_⟧[_]ᵗ) _

----------------------
-- Demand semantics --
----------------------

⟦_⟧ᵉ :
  (t : Γ ⊢ α)
  (γ : 𝔼.⟦ Γ ⟧ᶜ) →
  ⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ →
  ⟦ Γ ⟧≺ᵐ γ

⟦foldr_,_⟧ᵉ :
  (t₁ : Γ ⸴ α ⸴ `T β ⊢ β) →
  (t₂ : Γ ⊢ β) →
  (γ : 𝔼.⟦ Γ ⟧ᶜ) →
  (vs : List 𝔼.⟦ α ⟧ᵗ) →
  ⟦ β ⟧≺ᵗ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs →
  ⟦ Γ ⸴ `List α ⟧≺ᵐ (γ ⸴ vs)

⟦let-step₁_,_⟧ᵉ : (t₁ : Γ ⊢ α)
                  (t₂ : Γ ⸴ α ⊢ β)
                  (γ : 𝔼.⟦ Γ ⟧ᶜ)
                → ⟦ β ⟧≺ᵗ 𝔼.⟦ `let t₁ `in t₂ ⟧ᵉ γ
                → ⟦ Γ ⟧≺ᵐ γ

⟦if-step₁_,_,_⟧ᵉ : (t₁ : Γ ⊢ `Bool)
                   (t₂ t₃ : Γ ⊢ α)
                   (γ : 𝔼.⟦ Γ ⟧ᶜ)
                 → ⟦ α ⟧≺ᵗ 𝔼.⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ
                 → ⟦ Γ ⟧≺ᵐ γ

⟦foldr-step₁_,_,_⟧ᵉ : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                      (t₂ : Γ ⊢ β)
                      (t₃ : Γ ⊢ `List α)
                      (γ : 𝔼.⟦ Γ ⟧ᶜ)
                    → ⟦ β ⟧≺ᵗ 𝔼.⟦ `foldr t₁ t₂ t₃ ⟧ᵉ γ
                    → ⟦ Γ ⟧≺ᵐ γ

⟦ ` x                      ⟧ᵉ γ d         = return (⊥ᶜ [ ∈ᴸ⇒lookup∈ᴸtoList x ]≔ d)
⟦ `let t₁ `in t₂           ⟧ᵉ γ d₂        =
  ⟦let-step₁ t₁ , t₂ ⟧ᵉ γ d₂
⟦ `false                   ⟧ᵉ γ d         = ⊥ᵐ
⟦ `true                    ⟧ᵉ γ d         = ⊥ᵐ
⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ d₂₃       =
  ⟦if-step₁ t₁ , t₂ , t₃ ⟧ᵉ γ d₂₃
⟦ `[]                      ⟧ᵉ γ d         = ⊥ᵐ
⟦ t₁ `∷ t₂                 ⟧ᵉ γ (d₁ ∷ d₂) = ⟦ t₁ ⟧ᵉ γ d₁ ⊔ᵐ ⟦ t₂ ⟧ᵉ γ d₂
⟦ `foldr t₁ t₂ t₃          ⟧ᵉ γ d₁₂       =
  ⟦foldr-step₁ t₁ , t₂ , t₃ ⟧ᵉ γ d₁₂
⟦ `tick t                  ⟧ᵉ γ d         = do
  tick
  ⟦ t ⟧ᵉ γ d
⟦ `lazy t                  ⟧ᵉ γ (thunk d) = ⟦ t ⟧ᵉ γ d
⟦ `lazy t₁                 ⟧ᵉ γ undefined = ⊥ᵐ
⟦ `force t₁                ⟧ᵉ γ d         = ⟦ t₁ ⟧ᵉ γ (thunk d)

⟦if_,_⟧ᵉ :
  (t₂ t₃ : Γ ⊢ α)
  (γ : 𝔼.⟦ Γ ⟧ᶜ)
  (v : Bool) →
  ⟦ α ⟧≺ᵗ 𝔼.⟦if t₂ , t₃ ⟧ᵉ γ v →
  ⟦ Γ ⸴ `Bool ⟧≺ᵐ (γ ⸴ v)

⟦let-step₂_⟧ᵉ : (t₁ : Γ ⊢ α₁)
           (γ : 𝔼.⟦ Γ ⟧ᶜ)
         → ⟦ Γ ⸴ α₁ ⟧≺ᶜ (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ)
         → ⟦ Γ ⟧≺ᵐ γ

⟦let-step₁ t₁ , t₂ ⟧ᵉ γ d₂ = do
  δ  ← ⟦ t₂ ⟧ᵉ (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ) d₂
  ⟦let-step₂ t₁ ⟧ᵉ γ δ
⟦let-step₂ t₁ ⟧ᵉ γ (δ₁ ⸴ d₁) = do
  δ₂ ← ⟦ t₁ ⟧ᵉ γ d₁
  return (δ₁ ⊔ᶜ δ₂)

⟦if-step₂_⟧ᵉ : (t₁ : Γ ⊢ `Bool)
          (γ : 𝔼.⟦ Γ ⟧ᶜ)
        → ⟦ Γ ⸴ `Bool ⟧≺ᶜ (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ)
        → ⟦ Γ ⟧≺ᵐ γ

⟦if-step₁ t₁ , t₂ , t₃ ⟧ᵉ γ d₂₃ = do
  δ  ← ⟦if t₂ , t₃ ⟧ᵉ γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₂₃
  ⟦if-step₂ t₁ ⟧ᵉ γ δ
⟦if-step₂ t₁ ⟧ᵉ γ (δ₁ ⸴ d₁) = do
  δ₂ ← ⟦ t₁ ⟧ᵉ γ d₁
  return (δ₁ ⊔ᶜ δ₂)

⟦foldr-step₂_⟧ᵉ : (t₃ : Γ ⊢ `List α₁)
                  (γ : 𝔼.⟦ Γ ⟧ᶜ)
                → ⟦ Γ ⸴ `List α₁ ⟧≺ᶜ (γ ⸴ 𝔼.⟦ t₃ ⟧ᵉ γ)
                → ⟦ Γ ⟧≺ᵐ γ

⟦foldr-step₁ t₁ , t₂ , t₃ ⟧ᵉ γ d₁₂ = do
  δ  ← ⟦foldr t₁ , t₂ ⟧ᵉ γ (𝔼.⟦ t₃ ⟧ᵉ γ) d₁₂
  ⟦foldr-step₂ t₃ ⟧ᵉ γ δ
⟦foldr-step₂ t₃ ⟧ᵉ γ (δ₁ ⸴ d₃) = do
  δ₂ ← ⟦ t₃ ⟧ᵉ γ d₃
  return (δ₁ ⊔ᶜ δ₂)

⟦if t₂ , t₃ ⟧ᵉ γ false d = do
  δ ← ⟦ t₃ ⟧ᵉ γ d
  return (δ ⸴ false)
⟦if t₂ , t₃ ⟧ᵉ γ true  d = do
  δ ← ⟦ t₂ ⟧ᵉ γ d
  return (δ ⸴ true)

⟦foldr₂₂_,_⟧ᵉ : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                (t₂ : Γ ⊢ β)
                (γ : 𝔼.⟦ Γ ⟧ᶜ)
                (v : 𝔼.⟦ α ⟧ᵗ)
                (vs : 𝔼.⟦ `List α ⟧ᵗ)
              → ⟦ Γ ⸴ α ⸴ `T β ⟧≺ᶜ (γ ⸴ v ⸴ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs)
              → ⟦ Γ ⸴ `List α ⟧≺ᵐ (γ ⸴ (v ∷ vs))
⟦foldr₂₃⟧ᵉ : (γ : 𝔼.⟦ Γ ⟧ᶜ)
             (v : 𝔼.⟦ α ⟧ᵗ)
             (vs : List 𝔼.⟦ α ⟧ᵗ)
           → ⟦ Γ ⟧≺ᶜ γ
           → ⟦ α ⟧≺ᵗ v
           → ⟦ Γ ⸴ `T (`List α) ⟧≺ᶜ (γ ⸴ vs)
           → ⟦ Γ ⸴ `List α ⟧≺ᵐ (γ ⸴ (v ∷ vs))

⟦foldr′_,_⟧ᵉ : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
               (t₂ : Γ ⊢ β)
               (γ : 𝔼.⟦ Γ ⟧ᶜ)
               (vs : List 𝔼.⟦ α ⟧ᵗ)
             → ⟦ `T β ⟧≺ᵗ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs
             → ⟦ Γ ⸴ `T (`List α) ⟧≺ᵐ (γ ⸴ vs)

⟦foldr t₁ , t₂ ⟧ᵉ γ []       d₁ = do
  δ ← ⟦ t₂ ⟧ᵉ γ d₁
  return (δ ⸴ [])
⟦foldr t₁ , t₂ ⟧ᵉ γ (v ∷ vs) d₁ = do
  δ ← ⟦ t₁ ⟧ᵉ (γ ⸴ v ⸴ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs) d₁
  ⟦foldr₂₂ t₁ , t₂ ⟧ᵉ γ v vs δ
⟦foldr₂₂ t₁ , t₂ ⟧ᵉ γ v vs (δ₁ ⸴ d₂ ⸴ d₃) = do
  δ ← ⟦foldr′ t₁ , t₂ ⟧ᵉ γ vs d₃
  ⟦foldr₂₃⟧ᵉ γ v vs δ₁ d₂ δ
⟦foldr₂₃⟧ᵉ γ v vs δ₁ d₂ (δ₂ ⸴ d₄) =
  return (δ₁ ⊔ᶜ δ₂ ⸴ (d₂ ∷ d₄))

⟦foldr′₂₂⟧ : (γ : 𝔼.⟦ Γ ⟧ᶜ)
             (vs : List 𝔼.⟦ α ⟧ᵗ)
           → ⟦ Γ ⸴ `List α ⟧≺ᶜ (γ ⸴ vs)
           → ⟦ Γ ⸴ `T (`List α) ⟧≺ᵐ (γ ⸴ vs)

⟦foldr′ t₁ , t₂ ⟧ᵉ γ vs undefined  = ⊥ᵐ
⟦foldr′ t₁ , t₂ ⟧ᵉ γ vs (thunk d₁) = do
  δ ← ⟦foldr t₁ , t₂ ⟧ᵉ γ vs d₁
  ⟦foldr′₂₂⟧ γ vs δ
⟦foldr′₂₂⟧ γ vs (δ ⸴ d₂) =
  return (δ ⸴ thunk d₂)

-------------------------------------------------------------------
-- Proof that (≤, ⊔, ⊥) is a bounded join-semilattice on demands --
-------------------------------------------------------------------

≤ᵗ-refl : ∀ {v} → Reflexive ⟦ α ⟧[ v ≻_≤ᵗ_]
≤ᵗ-refl  {`Bool   } {x = false    } = false
≤ᵗ-refl  {`Bool   } {x = true     } = true
≤ᵗ-refl  {`T α    } {x = thunk d₁ } = thunk ≤ᵗ-refl
≤ᵗ-refl  {`T α    } {x = undefined} = undefined
≤ᵗ-refl  {`List α } {x = []       } = []
≤ᵗ-refl  {`List α } {x = d₁ ∷ d₂  } = ≤ᵗ-refl ∷ ≤ᵗ-refl

≤ᵗ-trans : ∀ {v} → Transitive ⟦ α ⟧[ v ≻_≤ᵗ_]
≤ᵗ-trans false           false           = false
≤ᵗ-trans true            true            = true
≤ᵗ-trans undefined       undefined       = undefined
≤ᵗ-trans undefined       (thunk d₂≤d₃)   = undefined
≤ᵗ-trans (thunk d₁≤d₂)   (thunk d₂≤d₃)   = thunk (≤ᵗ-trans d₁≤d₂ d₂≤d₃)
≤ᵗ-trans []              []              = []
≤ᵗ-trans (d₁≤d₂ ∷ d₁≤d₃) (d₂≤d₃ ∷ d₂≤d₄) = ≤ᵗ-trans d₁≤d₂ d₂≤d₃ ∷ ≤ᵗ-trans d₁≤d₃ d₂≤d₄

≤ᵗ-isPreorder : ∀ {v} → IsPreorder _≡_ ⟦ α ⟧[ v ≻_≤ᵗ_]
≤ᵗ-isPreorder = record
  { isEquivalence = ≡.isEquivalence
  ; reflexive     = λ{ refl → ≤ᵗ-refl }
  ; trans         = ≤ᵗ-trans
  }

≤ᵗ-antisym : ∀ {v} → Antisymmetric _≡_ ⟦ α ⟧[ v ≻_≤ᵗ_]
≤ᵗ-antisym false               false               = refl
≤ᵗ-antisym true                true                = refl
≤ᵗ-antisym undefined           undefined           = refl
≤ᵗ-antisym (thunk d₁₁≤d₂₁)     (thunk d₂₁≤d₁₁)     = cong thunk (≤ᵗ-antisym d₁₁≤d₂₁ d₂₁≤d₁₁)
≤ᵗ-antisym []                  []                  = refl
≤ᵗ-antisym (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) = cong₂ _∷_ (≤ᵗ-antisym d₁₁≤d₂₁ d₂₁≤d₃₁) (≤ᵗ-antisym d₁₂≤d₂₂ d₂₂≤d₃₂)

≤ᵗ-isPartialOrder : ∀ {v} → IsPartialOrder _≡_ ⟦ α ⟧[ v ≻_≤ᵗ_]
≤ᵗ-isPartialOrder = record
  { isPreorder = ≤ᵗ-isPreorder
  ; antisym    = ≤ᵗ-antisym
  }

d₁≤ᵗd₁⊔ᵗd₂ : ∀ {v} d₁ d₂ → ⟦ α ⟧[ v ≻ d₁ ≤ᵗ d₁ ⊔ᵗ d₂ ]
d₁≤ᵗd₁⊔ᵗd₂ false false = false
d₁≤ᵗd₁⊔ᵗd₂ true true = true
d₁≤ᵗd₁⊔ᵗd₂ (thunk d₁₁) (thunk d₂₁) = thunk (d₁≤ᵗd₁⊔ᵗd₂ d₁₁ d₂₁)
d₁≤ᵗd₁⊔ᵗd₂ (thunk d₁₁) undefined   = ≤ᵗ-refl
d₁≤ᵗd₁⊔ᵗd₂ undefined   (thunk d₂₁) = undefined
d₁≤ᵗd₁⊔ᵗd₂ undefined   undefined   = undefined
d₁≤ᵗd₁⊔ᵗd₂ []          []          = []
d₁≤ᵗd₁⊔ᵗd₂ (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = d₁≤ᵗd₁⊔ᵗd₂ d₁₁ d₂₁ ∷ d₁≤ᵗd₁⊔ᵗd₂ d₁₂ d₂₂

d₂≤ᵗd₁⊔ᵗd₂ : ∀ {v} d₁ d₂ → ⟦ α ⟧[ v ≻ d₂ ≤ᵗ d₁ ⊔ᵗ d₂ ]
d₂≤ᵗd₁⊔ᵗd₂ false       false       = false
d₂≤ᵗd₁⊔ᵗd₂ true        true        = true
d₂≤ᵗd₁⊔ᵗd₂ (thunk d₁₁) (thunk d₂₁) = thunk (d₂≤ᵗd₁⊔ᵗd₂ d₁₁ d₂₁)
d₂≤ᵗd₁⊔ᵗd₂ (thunk d₁₁) undefined   = undefined
d₂≤ᵗd₁⊔ᵗd₂ undefined   (thunk d₂₁) = ≤ᵗ-refl
d₂≤ᵗd₁⊔ᵗd₂ undefined   undefined   = undefined
d₂≤ᵗd₁⊔ᵗd₂ []          []          = []
d₂≤ᵗd₁⊔ᵗd₂ (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = d₂≤ᵗd₁⊔ᵗd₂ d₁₁ d₂₁ ∷ d₂≤ᵗd₁⊔ᵗd₂ d₁₂ d₂₂

⊔ᵗ-least : ∀ {v d₁ d₂ d₃} →
  ⟦ α ⟧[ v ≻ d₁ ≤ᵗ d₃ ] →
  ⟦ α ⟧[ v ≻ d₂ ≤ᵗ d₃ ] →
  ⟦ α ⟧[ v ≻ d₁ ⊔ᵗ d₂ ≤ᵗ d₃ ]
⊔ᵗ-least false               false               = false
⊔ᵗ-least true                true                = true
⊔ᵗ-least undefined           undefined           = undefined
⊔ᵗ-least undefined           (thunk d₂₁≤d₃₁)     = thunk d₂₁≤d₃₁
⊔ᵗ-least (thunk d₁₁≤d₂₁)     undefined           = thunk d₁₁≤d₂₁
⊔ᵗ-least (thunk d₁₁≤d₂₁)     (thunk d₂₁≤d₃₁)     = thunk (⊔ᵗ-least d₁₁≤d₂₁ d₂₁≤d₃₁)
⊔ᵗ-least []                  []                  = []
⊔ᵗ-least (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) = ⊔ᵗ-least d₁₁≤d₂₁ d₂₁≤d₃₁ ∷ ⊔ᵗ-least d₁₂≤d₂₂ d₂₂≤d₃₂

⊔ᵗ-supremum : ∀ {v} → Supremum ⟦ α ⟧[ v ≻_≤ᵗ_] _⊔ᵗ_
⊔ᵗ-supremum d₁ d₂ = d₁≤ᵗd₁⊔ᵗd₂ d₁ d₂ , d₂≤ᵗd₁⊔ᵗd₂ d₁ d₂ , λ _ → ⊔ᵗ-least

≤ᵗ-⊔ᵗ-isJoinSemilattice : ∀ {v} → IsJoinSemilattice _≡_ ⟦ α ⟧[ v ≻_≤ᵗ_] _⊔ᵗ_
≤ᵗ-⊔ᵗ-isJoinSemilattice = record
  { isPartialOrder = ≤ᵗ-isPartialOrder
  ; supremum       = ⊔ᵗ-supremum
  }

⊥ᵗ-minimum : ∀ {v} → Minimum ⟦ α ⟧[ v ≻_≤ᵗ_] (⊥⟦ α ⟧≺ᵗ v)
⊥ᵗ-minimum false      = false
⊥ᵗ-minimum true       = true
⊥ᵗ-minimum (thunk d₁) = undefined
⊥ᵗ-minimum undefined  = undefined
⊥ᵗ-minimum []         = []
⊥ᵗ-minimum (d₁ ∷ d₂)  = ⊥ᵗ-minimum d₁ ∷ undefined

≤ᵗ-⊔ᵗ-⊥ᵗ-isBoundedJoinSemilattice : ∀ {v} → IsBoundedJoinSemilattice _≡_ ⟦ α ⟧[ v ≻_≤ᵗ_] _⊔ᵗ_ (⊥⟦ α ⟧≺ᵗ v)
≤ᵗ-⊔ᵗ-⊥ᵗ-isBoundedJoinSemilattice = record
  { isJoinSemilattice = ≤ᵗ-⊔ᵗ-isJoinSemilattice
  ; minimum           = ⊥ᵗ-minimum
  }

---------------------------------------
-- Ditto the above, but for contexts --
---------------------------------------

≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] _⊔ᶜ_ (⊥⟦ Γ ⟧≺ᶜ γ)
≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice = AllPointwise.isBoundedJoinSemilattice ≤ᵗ-⊔ᵗ-⊥ᵗ-isBoundedJoinSemilattice

⊥ᶜ-minimum : Minimum ⟦ Γ ⟧[ γ ≻_≤ᶜ_] (⊥⟦ Γ ⟧≺ᶜ γ)
⊥ᶜ-minimum = ≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice .IsBoundedJoinSemilattice.minimum

≤ᶜ-⊔ᶜ-isJoinSemilattice : ∀ {γ} → IsJoinSemilattice _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] _⊔ᶜ_
≤ᶜ-⊔ᶜ-isJoinSemilattice =
  ≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice .IsBoundedJoinSemilattice.isJoinSemilattice

≤ᶜ-⊔ᶜ-JoinSemilattice : 𝔼.⟦ Γ ⟧ᶜ → JoinSemilattice _ _ _
≤ᶜ-⊔ᶜ-JoinSemilattice γ = record
  { Carrier           = ≺ᶜ γ
  ; _≈_               = _≡_
  ; _≤_               = _≤ᶜ_
  ; _∨_               = _⊔ᶜ_
  ; isJoinSemilattice = ≤ᶜ-⊔ᶜ-isJoinSemilattice
  }

δ₁≤δ₁⊔δ₂ : (δ₁ δ₂ : ⟦ Γ ⟧≺ᶜ γ) → δ₁ ≤ᶜ δ₁ ⊔ᶜ δ₂
δ₁≤δ₁⊔δ₂ δ₁ δ₂ = ≤ᶜ-⊔ᶜ-isJoinSemilattice .IsJoinSemilattice.supremum δ₁ δ₂ .proj₁

δ₂≤δ₁⊔δ₂ : (δ₁ δ₂ : ⟦ Γ ⟧≺ᶜ γ) → δ₂ ≤ᶜ δ₁ ⊔ᶜ δ₂
δ₂≤δ₁⊔δ₂ δ₁ δ₂ = ≤ᶜ-⊔ᶜ-isJoinSemilattice .IsJoinSemilattice.supremum δ₁ δ₂ .proj₂ .proj₁

⊔ᶜ-monotonic : _⊔ᶜ_ Preserves₂ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
⊔ᶜ-monotonic = Relation.Binary.Lattice.Properties.JoinSemilattice.∨-monotonic (≤ᶜ-⊔ᶜ-JoinSemilattice _)

≤ᶜ-⊔ᶜ-isPartialOrder : IsPartialOrder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-⊔ᶜ-isPartialOrder = ≤ᶜ-⊔ᶜ-isJoinSemilattice .IsJoinSemilattice.isPartialOrder

≤ᶜ-⊔ᶜ-isPreorder : IsPreorder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-⊔ᶜ-isPreorder = ≤ᶜ-⊔ᶜ-isPartialOrder .IsPartialOrder.isPreorder

≤ᶜ-refl : Reflexive ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-refl = ≤ᶜ-⊔ᶜ-isPreorder .IsPreorder.reflexive refl

--------------------------------------------------
-- Ditto the above, but for contexts with costs --
--------------------------------------------------

⊥ᵐ-minimum : Minimum ⟦ Γ ⟧[ γ ≻_≤ᵐ_] (⊥⟦ Γ ⟧≺ᵐ γ)
⊥ᵐ-minimum {Γ = Γ} {γ = γ} = ×.minimum {_≤₁_ = ⟦ Γ ⟧[ γ ≻_≤ᶜ_]} {_≤₂_ = ℕ._≤_} ⊥ᶜ-minimum (λ _ → z≤n)

⊔ᵐ-monotonic : _⊔ᵐ_ Preserves₂ ⟦ Γ ⟧[ γ ≻_≤ᵐ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᵐ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
⊔ᵐ-monotonic {Γ = Γ} {γ = γ} = ×.preserves₂ {_∼₁_ = ⟦ Γ ⟧[ γ ≻_≤ᶜ_]} {_∼₂_ = ℕ._≤_} ⊔ᶜ-monotonic +-mono-≤

≤ᵐ-⊔ᵐ-isPartialOrder : IsPartialOrder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-⊔ᵐ-isPartialOrder = ×.isPartialOrder ≤ᶜ-⊔ᶜ-isPartialOrder ℕ.≤-isPartialOrder

≤ᵐ-⊔ᵐ-isPreorder : IsPreorder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-⊔ᵐ-isPreorder = ≤ᵐ-⊔ᵐ-isPartialOrder .IsPartialOrder.isPreorder

≤ᵐ-refl : Reflexive ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-refl = ≤ᵐ-⊔ᵐ-isPreorder .IsPreorder.reflexive refl

>>=-mono : {γ₁ : 𝔼.⟦ Γ₁ ⟧ᶜ} {γ₂ : 𝔼.⟦ Γ₂ ⟧ᶜ}
           {m₁ m₂ : ⟦ Γ₁ ⟧≺ᵐ γ₁} {k₁ k₂ : ≺ᶜ γ₁ → ≺ᵐ γ₂}
         → m₁ ≤ᵐ m₂
         → (∀ {δ₁ δ₂} → δ₁ ≤ᶜ δ₂ → k₁ δ₁ ≤ᵐ k₂ δ₂)
         → (m₁ >>= k₁) ≤ᵐ (m₂ >>= k₂)
>>=-mono (p₁ , p₂) q = q p₁ .proj₁ , +-mono-≤ p₂ (q p₁ .proj₂)

>>=-monoˡ : {γ₁ : 𝔼.⟦ Γ₁ ⟧ᶜ} {γ₂ : 𝔼.⟦ Γ₂ ⟧ᶜ}
            {m₁ m₂ : ⟦ Γ₁ ⟧≺ᵐ γ₁}
            {k : ≺ᶜ γ₁ → ≺ᵐ γ₂}
          → m₁ ≤ᵐ m₂
          → (∀ {δ₁ δ₂} → δ₁ ≤ᶜ δ₂ → k δ₁ ≤ᵐ k δ₂)
          → (m₁ >>= k) ≤ᵐ (m₂ >>= k)
>>=-monoˡ = >>=-mono

return-mono : {δ₁ δ₂ : ⟦ Γ₁ ⟧≺ᶜ γ}
            → δ₁ ≤ᶜ δ₂
            → return δ₁ ≤ᵐ return δ₂
return-mono δ₁≤δ₂ = δ₁≤δ₂ , ≤-refl

--------------------------------------
-- Monotonicity of demand semantics --
--------------------------------------

⟦_⟧ᵉ-mono : (t : Γ ⊢ α)
            (γ : 𝔼.⟦ Γ ⟧ᶜ)
            {d d′ : ⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ}
          → d ≤ᵗ d′
          → ⟦ t ⟧ᵉ γ d ≤ᵐ ⟦ t ⟧ᵉ γ d′

⟦if_,_⟧ᵉ-mono : (t₂ t₃ : Γ ⊢ α)
                (γ : 𝔼.⟦ Γ ⟧ᶜ)
                (v : Bool)
                {d₂₃ d₂₃′ : ⟦ α ⟧≺ᵗ 𝔼.⟦if t₂ , t₃ ⟧ᵉ γ v}
              → d₂₃ ≤ᵗ d₂₃′
              → ⟦if t₂ , t₃ ⟧ᵉ γ v d₂₃ ≤ᵐ ⟦if t₂ , t₃ ⟧ᵉ γ v d₂₃′

⟦foldr_,_⟧ᵉ-mono : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                   (t₂ : Γ ⊢ β)
                   (γ : 𝔼.⟦ Γ ⟧ᶜ)
                   (vs : List 𝔼.⟦ α ⟧ᵗ)
                   {d₁₂ d₁₂′ : ⟦ β ⟧≺ᵗ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs}
                 → d₁₂ ≤ᵗ d₁₂′
                 → ⟦foldr t₁ , t₂ ⟧ᵉ γ vs d₁₂ ≤ᵐ ⟦foldr t₁ , t₂ ⟧ᵉ γ vs d₁₂′

⟦ ` x                      ⟧ᵉ-mono γ d≤d′                =
  return-mono (AllPointwise.updateAt (∈ᴸ⇒lookup∈ᴸtoList x) (const d≤d′) ≤ᶜ-refl)
⟦ `let t₁ `in t₂           ⟧ᵉ-mono γ d₂≤d₂′              =
  >>=-monoˡ
    {k = ⟦let-step₂ t₁ ⟧ᵉ γ}
    (⟦ t₂ ⟧ᵉ-mono (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ) d₂≤d₂′)
    (λ{ (δ₁≤δ₁′ ⸴ d₁≤d₁′) →
      >>=-mono
        (⟦ t₁ ⟧ᵉ-mono γ d₁≤d₁′)
        (λ δ₂≤δ₂′ → return-mono (⊔ᶜ-monotonic δ₁≤δ₁′ δ₂≤δ₂′)) })
⟦ `false                   ⟧ᵉ-mono γ d≤d′                = ≤ᵐ-refl
⟦ `true                    ⟧ᵉ-mono γ d≤d′                = ≤ᵐ-refl
⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ-mono γ d₂₃≤d₂₃′            =
  >>=-monoˡ
    {k = ⟦if-step₂ t₁ ⟧ᵉ γ}
    (⟦if t₂ , t₃ ⟧ᵉ-mono γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₂₃≤d₂₃′)
    (λ{ (δ₁≤δ₁′ ⸴ d₁≤d₁′) →
      >>=-mono
        (⟦ t₁ ⟧ᵉ-mono γ d₁≤d₁′)
        (λ δ₂≤δ₂′ → return-mono (⊔ᶜ-monotonic δ₁≤δ₁′ δ₂≤δ₂′) )})
⟦ `[]                      ⟧ᵉ-mono γ d≤d′                = ≤ᵐ-refl
⟦ t₁ `∷ t₂                 ⟧ᵉ-mono γ (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) =
  ⊔ᵐ-monotonic (⟦ t₁ ⟧ᵉ-mono γ d₁₁≤d₂₁) (⟦ t₂ ⟧ᵉ-mono γ d₁₂≤d₂₂)
⟦ `foldr t₁ t₂ t₃          ⟧ᵉ-mono γ d₁₂≤d₁₂′            =
  >>=-monoˡ
    {k = ⟦foldr-step₂ t₃ ⟧ᵉ γ}
    (⟦foldr t₁ , t₂ ⟧ᵉ-mono γ (𝔼.⟦ t₃ ⟧ᵉ γ) d₁₂≤d₁₂′)
    (λ{ (δ₁≤δ₁′ ⸴ d₃≤d₃′) →
      >>=-mono
        (⟦ t₃ ⟧ᵉ-mono γ d₃≤d₃′)
        (λ δ₂≤δ₂′ → return-mono (⊔ᶜ-monotonic δ₁≤δ₁′ δ₂≤δ₂′)) })
⟦ `tick t₁                 ⟧ᵉ-mono γ d₁≤d₁′              =
  let (δ≤δ′ , n≤n′) = ⟦ t₁ ⟧ᵉ-mono γ d₁≤d₁′
  in δ≤δ′ , s≤s n≤n′
⟦ `lazy t₁                 ⟧ᵉ-mono γ undefined           = ⊥ᵐ-minimum _
⟦ `lazy t₁                 ⟧ᵉ-mono γ (thunk d₁≤d₁′)      = ⟦ t₁ ⟧ᵉ-mono γ d₁≤d₁′
⟦ `force t₁                ⟧ᵉ-mono γ d≤d′                = ⟦ t₁ ⟧ᵉ-mono γ (thunk d≤d′)

⟦if t₂ , t₃ ⟧ᵉ-mono γ false d₂₃≤d₂₃′ =
  >>=-mono
    (⟦ t₃ ⟧ᵉ-mono γ d₂₃≤d₂₃′)
    (λ δ≤δ′ → return-mono (δ≤δ′ ⸴ false))
⟦if t₂ , t₃ ⟧ᵉ-mono γ true d₂₃≤d₂₃′  =
  >>=-mono
    (⟦ t₂ ⟧ᵉ-mono γ d₂₃≤d₂₃′)
    (λ δ≤δ′ → return-mono (δ≤δ′ ⸴ true))

⟦foldr′_,_⟧ᵉ-mono : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                    (t₂ : Γ ⊢ β)
                    (γ : 𝔼.⟦ Γ ⟧ᶜ)
                    (vs : List 𝔼.⟦ α ⟧ᵗ)
                    {d₁ d₁′ : ⟦ `T β ⟧≺ᵗ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs}
                  → d₁ ≤ᵗ d₁′
                  → ⟦foldr′ t₁ , t₂ ⟧ᵉ γ vs d₁ ≤ᵐ ⟦foldr′ t₁ , t₂ ⟧ᵉ γ vs d₁′
⟦foldr′ t₁ , t₂ ⟧ᵉ-mono γ vs undefined      = ⊥ᵐ-minimum _
⟦foldr′ t₁ , t₂ ⟧ᵉ-mono γ vs (thunk d₁≤d₁′) =
  >>=-monoˡ
    {k = ⟦foldr′₂₂⟧ γ vs}
    (⟦foldr t₁ , t₂ ⟧ᵉ-mono γ vs d₁≤d₁′)
    (λ{ (δ≤δ′ ⸴ d₂≤d₂′) → return-mono (δ≤δ′ ⸴ thunk d₂≤d₂′) })

⟦foldr t₁ , t₂ ⟧ᵉ-mono γ []       d₁₂≤d₁₂′ =
  >>=-monoˡ
    (⟦ t₂ ⟧ᵉ-mono γ d₁₂≤d₁₂′)
    (λ δ≤δ′ → return-mono (δ≤δ′ ⸴ []))
⟦foldr t₁ , t₂ ⟧ᵉ-mono γ (v ∷ vs) d₁₂≤d₁₂′ =
  >>=-monoˡ
    {k = ⟦foldr₂₂ t₁ , t₂ ⟧ᵉ γ v vs}
    (⟦ t₁ ⟧ᵉ-mono (γ ⸴ v ⸴ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs) d₁₂≤d₁₂′)
    (λ{ (δ₁≤δ₁′ ⸴ d₂≤d₂′ ⸴ d₃≤d₃′) →
      >>=-mono
        {k₁ = ⟦foldr₂₃⟧ᵉ γ v vs _ _}
        {k₂ = ⟦foldr₂₃⟧ᵉ γ v vs _ _}
        (⟦foldr′ t₁ , t₂ ⟧ᵉ-mono γ vs d₃≤d₃′)
        (λ{ (δ₂≤δ₂′ ⸴ d₄≤d₄′) → return-mono (⊔ᶜ-monotonic δ₁≤δ₁′ δ₂≤δ₂′ ⸴ (d₂≤d₂′ ∷ d₄≤d₄′)) }) })
