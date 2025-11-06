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
open import LogicalLaziness.Base.Data.List.All
open import LogicalLaziness.Base.Data.List.Membership.Propositional
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

-- `⟦ α ⟧≺ᵉ v` describes the set of demands in `α` that approximate the total
-- value `v`.
infix 4 ⟦_⟧≺ᵉ_
data ⟦_⟧≺ᵉ_ : (α : Ty) → 𝔼.⟦ α ⟧ᵗ → Type where
  false     : ⟦ `Bool ⟧≺ᵉ false
  true      : ⟦ `Bool ⟧≺ᵉ true
  thunk     : {v : 𝔼.⟦ α ⟧ᵗ}
            → ⟦ α ⟧≺ᵉ v
            → ⟦ `T α ⟧≺ᵉ v
  undefined : {v : 𝔼.⟦ α ⟧ᵗ}
            → ⟦ `T α ⟧≺ᵉ v
  []        : ⟦ `List α ⟧≺ᵉ []
  _∷_       : {v : 𝔼.⟦ α ⟧ᵗ} {vs : List 𝔼.⟦ α ⟧ᵗ}
            → ⟦ α ⟧≺ᵉ v
            → ⟦ `T (`List α) ⟧≺ᵉ vs
            → ⟦ `List α ⟧≺ᵉ v ∷ vs

-- Now we introduce a join-semilattice (≤, ⊔, ⊥) of demands (on a fixed value).
-- We do not prove any properties yet.

infix 4 ⟦_⟧[_≻_≤ᵉ_]
data ⟦_⟧[_≻_≤ᵉ_] : (α : Ty) (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧≺ᵉ v → ⟦ α ⟧≺ᵉ v → Type where
  false     : ⟦ `Bool ⟧[ false ≻ false ≤ᵉ false ]
  true      : ⟦ `Bool ⟧[ true  ≻ true  ≤ᵉ true  ]
  undefined : ∀ {v d}
            → ⟦ `T α ⟧[ v ≻ undefined ≤ᵉ d ]
  thunk     : ∀ {v d₁ d₂}
            → ⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₂ ]
            → ⟦ `T α ⟧[ v ≻ thunk d₁ ≤ᵉ thunk d₂ ]
  []        : ⟦ `List α ⟧[ [] ≻ [] ≤ᵉ [] ]
  _∷_       : ∀ {v₁ v₂ d₁₁ d₁₂ d₂₁ d₂₂}
            → ⟦ α ⟧[ v₁ ≻ d₁₁ ≤ᵉ d₁₂ ]
            → ⟦ `T (`List α) ⟧[ v₂ ≻ d₂₁ ≤ᵉ d₂₂ ]
            → ⟦ `List α ⟧[ v₁ ∷ v₂ ≻ d₁₁ ∷ d₂₁ ≤ᵉ d₁₂ ∷ d₂₂ ]

infix 4 _≤ᵉ_
_≤ᵉ_ : {α : Ty} {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧≺ᵉ v → ⟦ α ⟧≺ᵉ v → Type
_≤ᵉ_ = ⟦ _ ⟧[ _ ≻_≤ᵉ_]

-- `d₁ ⊔ᵉ d₂` is the join of the demands `d₁` and `d₂`.
infixl 6 _⊔ᵉ_
_⊔ᵉ_ : {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧≺ᵉ v → ⟦ α ⟧≺ᵉ v → ⟦ α ⟧≺ᵉ v
false       ⊔ᵉ false       = false
true        ⊔ᵉ true        = true
thunk d₁    ⊔ᵉ thunk d₂    = thunk (d₁ ⊔ᵉ d₂)
thunk d₁    ⊔ᵉ undefined   = thunk d₁
undefined   ⊔ᵉ thunk d₂    = thunk d₂
undefined   ⊔ᵉ undefined   = undefined
[]          ⊔ᵉ []          = []
(d₁₁ ∷ d₁₂) ⊔ᵉ (d₂₁ ∷ d₂₂) = d₁₁ ⊔ᵉ d₂₁ ∷ d₁₂ ⊔ᵉ d₂₂

-- `⊥⟦ α ⟧≺ᵉ v` is the least demand in `α` on the total value `v`.
infix 4 ⊥⟦_⟧≺ᵉ_
⊥⟦_⟧≺ᵉ_ : ∀ α (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧≺ᵉ v
⊥⟦ `Bool   ⟧≺ᵉ false   = false
⊥⟦ `Bool   ⟧≺ᵉ true     = true
⊥⟦ `T α    ⟧≺ᵉ v        = undefined
⊥⟦ `List α ⟧≺ᵉ []       = []
⊥⟦ `List α ⟧≺ᵉ (v ∷ vs) = (⊥⟦ α ⟧≺ᵉ v) ∷ undefined

⊥ᵉ : ∀ {α} {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧≺ᵉ v
⊥ᵉ = ⊥⟦ _ ⟧≺ᵉ _

-----------------------------------------------------
-- The bounded join-semilattice of demand contexts --
-----------------------------------------------------

-- A demand context on an evaluation context `γ` (itself over a typing context
-- `Γ`) assigns to each value `v` in `γ` some demand on `v`.

infix 4 ⟦_⟧≺ᶜ_
⟦_⟧≺ᶜ_ : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → Type
⟦ Γ ⟧≺ᶜ γ = All (uncurry ⟦_⟧≺ᵉ_) (All.toList γ)

infix 4 ≺ᶜ_
≺ᶜ_ : 𝔼.⟦ Γ ⟧ᶜ → Type
≺ᶜ γ = All (uncurry ⟦_⟧≺ᵉ_) (All.toList γ)

private
  variable
    δ δ₁ δ₂ δ₃ : ≺ᶜ γ

-- The bounded join-semilattice of demands can be extended pointwise to a
-- bounded join-semilattice of demand contexts.

infix 4 ⟦_⟧[_≻_≤ᶜ_]
⟦_⟧[_≻_≤ᶜ_] : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → ≺ᶜ γ → ≺ᶜ γ → Type
⟦ Γ ⟧[ γ ≻ δ₁ ≤ᶜ δ₂ ] = AllPointwise _≤ᵉ_ δ₁ δ₂

infix 4 _≤ᶜ_
_≤ᶜ_ : ≺ᶜ γ → ≺ᶜ γ → Type
δ₁ ≤ᶜ δ₂ = ⟦ _ ⟧[ _ ≻ δ₁ ≤ᶜ δ₂ ]

infixl 6 _⊔ᶜ_
_⊔ᶜ_ : ≺ᶜ γ → ≺ᶜ γ → ≺ᶜ γ
δ₁ ⊔ᶜ δ₂ = All.zipWith (uncurry _⊔ᵉ_) (δ₁ , δ₂)

-- `⊥⟦ Γ ⟧≺ᶜ γ` is the least demand context of shape `Γ` on the evaluation
-- context `γ`.
infix 4 ⊥⟦_⟧≺ᶜ_
⊥⟦_⟧≺ᶜ_ : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → ⟦ Γ ⟧≺ᶜ γ
⊥⟦ Γ ⟧≺ᶜ γ = All.universal (λ _ → ⊥ᵉ) (All.toList γ)

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

----------------------
-- Demand semantics --
----------------------

⟦_⟧ᵉ :
  (t : Γ ⊢ α)
  (γ : 𝔼.⟦ Γ ⟧ᶜ) →
  ⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ →
  ⟦ Γ ⟧≺ᵐ γ

⟦foldr_,_⟧ᵉ :
  (t₁ : Γ ⸴ α ⸴ `T β ⊢ β) →
  (t₂ : Γ ⊢ β) →
  (γ : 𝔼.⟦ Γ ⟧ᶜ) →
  (vs : List 𝔼.⟦ α ⟧ᵗ) →
  ⟦ β ⟧≺ᵉ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs →
  ⟦ Γ ⸴ `List α ⟧≺ᵐ (γ ⸴ vs)

⟦let-step₁_,_⟧ᵉ : (t₁ : Γ ⊢ α)
                  (t₂ : Γ ⸴ α ⊢ β)
                  (γ : 𝔼.⟦ Γ ⟧ᶜ)
                → ⟦ β ⟧≺ᵉ 𝔼.⟦ `let t₁ `in t₂ ⟧ᵉ γ
                → ⟦ Γ ⟧≺ᵐ γ

⟦if-step₁_,_,_⟧ᵉ : (t₁ : Γ ⊢ `Bool)
                   (t₂ t₃ : Γ ⊢ α)
                   (γ : 𝔼.⟦ Γ ⟧ᶜ)
                 → ⟦ α ⟧≺ᵉ 𝔼.⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ
                 → ⟦ Γ ⟧≺ᵐ γ

⟦foldr-step₁_,_,_⟧ᵉ : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                      (t₂ : Γ ⊢ β)
                      (t₃ : Γ ⊢ `List α)
                      (γ : 𝔼.⟦ Γ ⟧ᶜ)
                    → ⟦ β ⟧≺ᵉ 𝔼.⟦ `foldr t₁ t₂ t₃ ⟧ᵉ γ
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
  ⟦ α ⟧≺ᵉ 𝔼.⟦if t₂ , t₃ ⟧ᵉ γ v →
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
           → ⟦ α ⟧≺ᵉ v
           → ⟦ Γ ⸴ `T (`List α) ⟧≺ᶜ (γ ⸴ vs)
           → ⟦ Γ ⸴ `List α ⟧≺ᵐ (γ ⸴ (v ∷ vs))

⟦foldr′_,_⟧ᵉ : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
               (t₂ : Γ ⊢ β)
               (γ : 𝔼.⟦ Γ ⟧ᶜ)
               (vs : List 𝔼.⟦ α ⟧ᵗ)
             → ⟦ `T β ⟧≺ᵉ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs
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

≤ᵉ-refl : ∀ {v} → Reflexive ⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-refl  {`Bool   } {x = false    } = false
≤ᵉ-refl  {`Bool   } {x = true     } = true
≤ᵉ-refl  {`T α    } {x = thunk d₁ } = thunk ≤ᵉ-refl
≤ᵉ-refl  {`T α    } {x = undefined} = undefined
≤ᵉ-refl  {`List α } {x = []       } = []
≤ᵉ-refl  {`List α } {x = d₁ ∷ d₂  } = ≤ᵉ-refl ∷ ≤ᵉ-refl

≤ᵉ-trans : ∀ {v} → Transitive ⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-trans false           false           = false
≤ᵉ-trans true            true            = true
≤ᵉ-trans undefined       undefined       = undefined
≤ᵉ-trans undefined       (thunk d₂≤d₃)   = undefined
≤ᵉ-trans (thunk d₁≤d₂)   (thunk d₂≤d₃)   = thunk (≤ᵉ-trans d₁≤d₂ d₂≤d₃)
≤ᵉ-trans []              []              = []
≤ᵉ-trans (d₁≤d₂ ∷ d₁≤d₃) (d₂≤d₃ ∷ d₂≤d₄) = ≤ᵉ-trans d₁≤d₂ d₂≤d₃ ∷ ≤ᵉ-trans d₁≤d₃ d₂≤d₄

≤ᵉ-isPreorder : ∀ {v} → IsPreorder _≡_ ⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-isPreorder = record
  { isEquivalence = ≡.isEquivalence
  ; reflexive     = λ{ refl → ≤ᵉ-refl }
  ; trans         = ≤ᵉ-trans
  }

≤ᵉ-antisym : ∀ {v} → Antisymmetric _≡_ ⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-antisym false               false               = refl
≤ᵉ-antisym true                true                = refl
≤ᵉ-antisym undefined           undefined           = refl
≤ᵉ-antisym (thunk d₁₁≤d₂₁)     (thunk d₂₁≤d₁₁)     = cong thunk (≤ᵉ-antisym d₁₁≤d₂₁ d₂₁≤d₁₁)
≤ᵉ-antisym []                  []                  = refl
≤ᵉ-antisym (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) = cong₂ _∷_ (≤ᵉ-antisym d₁₁≤d₂₁ d₂₁≤d₃₁) (≤ᵉ-antisym d₁₂≤d₂₂ d₂₂≤d₃₂)

≤ᵉ-isPartialOrder : ∀ {v} → IsPartialOrder _≡_ ⟦ α ⟧[ v ≻_≤ᵉ_]
≤ᵉ-isPartialOrder = record
  { isPreorder = ≤ᵉ-isPreorder
  ; antisym    = ≤ᵉ-antisym
  }

d₁≤ᵉd₁⊔ᵉd₂ : ∀ {v} d₁ d₂ → ⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₁ ⊔ᵉ d₂ ]
d₁≤ᵉd₁⊔ᵉd₂ false false = false
d₁≤ᵉd₁⊔ᵉd₂ true true = true
d₁≤ᵉd₁⊔ᵉd₂ (thunk d₁₁) (thunk d₂₁) = thunk (d₁≤ᵉd₁⊔ᵉd₂ d₁₁ d₂₁)
d₁≤ᵉd₁⊔ᵉd₂ (thunk d₁₁) undefined   = ≤ᵉ-refl
d₁≤ᵉd₁⊔ᵉd₂ undefined   (thunk d₂₁) = undefined
d₁≤ᵉd₁⊔ᵉd₂ undefined   undefined   = undefined
d₁≤ᵉd₁⊔ᵉd₂ []          []          = []
d₁≤ᵉd₁⊔ᵉd₂ (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = d₁≤ᵉd₁⊔ᵉd₂ d₁₁ d₂₁ ∷ d₁≤ᵉd₁⊔ᵉd₂ d₁₂ d₂₂

d₂≤ᵉd₁⊔ᵉd₂ : ∀ {v} d₁ d₂ → ⟦ α ⟧[ v ≻ d₂ ≤ᵉ d₁ ⊔ᵉ d₂ ]
d₂≤ᵉd₁⊔ᵉd₂ false       false       = false
d₂≤ᵉd₁⊔ᵉd₂ true        true        = true
d₂≤ᵉd₁⊔ᵉd₂ (thunk d₁₁) (thunk d₂₁) = thunk (d₂≤ᵉd₁⊔ᵉd₂ d₁₁ d₂₁)
d₂≤ᵉd₁⊔ᵉd₂ (thunk d₁₁) undefined   = undefined
d₂≤ᵉd₁⊔ᵉd₂ undefined   (thunk d₂₁) = ≤ᵉ-refl
d₂≤ᵉd₁⊔ᵉd₂ undefined   undefined   = undefined
d₂≤ᵉd₁⊔ᵉd₂ []          []          = []
d₂≤ᵉd₁⊔ᵉd₂ (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = d₂≤ᵉd₁⊔ᵉd₂ d₁₁ d₂₁ ∷ d₂≤ᵉd₁⊔ᵉd₂ d₁₂ d₂₂

⊔ᵉ-least : ∀ {v d₁ d₂ d₃} →
  ⟦ α ⟧[ v ≻ d₁ ≤ᵉ d₃ ] →
  ⟦ α ⟧[ v ≻ d₂ ≤ᵉ d₃ ] →
  ⟦ α ⟧[ v ≻ d₁ ⊔ᵉ d₂ ≤ᵉ d₃ ]
⊔ᵉ-least false               false               = false
⊔ᵉ-least true                true                = true
⊔ᵉ-least undefined           undefined           = undefined
⊔ᵉ-least undefined           (thunk d₂₁≤d₃₁)     = thunk d₂₁≤d₃₁
⊔ᵉ-least (thunk d₁₁≤d₂₁)     undefined           = thunk d₁₁≤d₂₁
⊔ᵉ-least (thunk d₁₁≤d₂₁)     (thunk d₂₁≤d₃₁)     = thunk (⊔ᵉ-least d₁₁≤d₂₁ d₂₁≤d₃₁)
⊔ᵉ-least []                  []                  = []
⊔ᵉ-least (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) (d₂₁≤d₃₁ ∷ d₂₂≤d₃₂) = ⊔ᵉ-least d₁₁≤d₂₁ d₂₁≤d₃₁ ∷ ⊔ᵉ-least d₁₂≤d₂₂ d₂₂≤d₃₂

⊔ᵉ-supremum : ∀ {v} → Supremum ⟦ α ⟧[ v ≻_≤ᵉ_] _⊔ᵉ_
⊔ᵉ-supremum d₁ d₂ = d₁≤ᵉd₁⊔ᵉd₂ d₁ d₂ , d₂≤ᵉd₁⊔ᵉd₂ d₁ d₂ , λ _ → ⊔ᵉ-least

≤ᵉ-⊔ᵉ-isJoinSemilattice : ∀ {v} → IsJoinSemilattice _≡_ ⟦ α ⟧[ v ≻_≤ᵉ_] _⊔ᵉ_
≤ᵉ-⊔ᵉ-isJoinSemilattice = record
  { isPartialOrder = ≤ᵉ-isPartialOrder
  ; supremum       = ⊔ᵉ-supremum
  }

⊥ᵉ-minimum : ∀ {v} → Minimum ⟦ α ⟧[ v ≻_≤ᵉ_] (⊥⟦ α ⟧≺ᵉ v)
⊥ᵉ-minimum false      = false
⊥ᵉ-minimum true       = true
⊥ᵉ-minimum (thunk d₁) = undefined
⊥ᵉ-minimum undefined  = undefined
⊥ᵉ-minimum []         = []
⊥ᵉ-minimum (d₁ ∷ d₂)  = ⊥ᵉ-minimum d₁ ∷ undefined

≤ᵉ-⊔ᵉ-⊥ᵉ-isBoundedJoinSemilattice : ∀ {v} → IsBoundedJoinSemilattice _≡_ ⟦ α ⟧[ v ≻_≤ᵉ_] _⊔ᵉ_ (⊥⟦ α ⟧≺ᵉ v)
≤ᵉ-⊔ᵉ-⊥ᵉ-isBoundedJoinSemilattice = record
  { isJoinSemilattice = ≤ᵉ-⊔ᵉ-isJoinSemilattice
  ; minimum           = ⊥ᵉ-minimum
  }

---------------------------------------
-- Ditto the above, but for contexts --
---------------------------------------

≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] _⊔ᶜ_ (⊥⟦ Γ ⟧≺ᶜ γ)
≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice = AllPointwise.isBoundedJoinSemilattice ≤ᵉ-⊔ᵉ-⊥ᵉ-isBoundedJoinSemilattice

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
            {d d′ : ⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ}
          → d ≤ᵉ d′
          → ⟦ t ⟧ᵉ γ d ≤ᵐ ⟦ t ⟧ᵉ γ d′

⟦if_,_⟧ᵉ-mono : (t₂ t₃ : Γ ⊢ α)
                (γ : 𝔼.⟦ Γ ⟧ᶜ)
                (v : Bool)
                {d₂₃ d₂₃′ : ⟦ α ⟧≺ᵉ 𝔼.⟦if t₂ , t₃ ⟧ᵉ γ v}
              → d₂₃ ≤ᵉ d₂₃′
              → ⟦if t₂ , t₃ ⟧ᵉ γ v d₂₃ ≤ᵐ ⟦if t₂ , t₃ ⟧ᵉ γ v d₂₃′

⟦foldr_,_⟧ᵉ-mono : (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                   (t₂ : Γ ⊢ β)
                   (γ : 𝔼.⟦ Γ ⟧ᶜ)
                   (vs : List 𝔼.⟦ α ⟧ᵗ)
                   {d₁₂ d₁₂′ : ⟦ β ⟧≺ᵉ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs}
                 → d₁₂ ≤ᵉ d₁₂′
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
                    {d₁ d₁′ : ⟦ `T β ⟧≺ᵉ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ vs}
                  → d₁ ≤ᵉ d₁′
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
