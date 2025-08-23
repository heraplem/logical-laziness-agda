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
open import Data.List
open import Data.List.Relation.Unary.All
  as All
import Data.List.Relation.Binary.Pointwise
  as List
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  as ×

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Effect.Monad.Tick
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
    α α₁ α₂ : Ty
    γ : 𝔼.⟦ Γ ⟧ᶜ
    γ₁ : 𝔼.⟦ Γ₁ ⟧ᶜ
    γ₂ : 𝔼.⟦ Γ₂ ⟧ᶜ

---------------------------------------------
-- The bounded join-semilattice of demands --
---------------------------------------------

-- `⟦ α ⟧ᵗ≺ v` describes the set of demands in `α` that approximate the total
-- value `v`.
infix 4 ⟦_⟧ᵗ≺_
data ⟦_⟧ᵗ≺_ : (α : Ty) → 𝔼.⟦ α ⟧ᵗ → Type where
  false     : ⟦ `Bool ⟧ᵗ≺ false
  true      : ⟦ `Bool ⟧ᵗ≺ true
  thunk     : {v : 𝔼.⟦ α₁ ⟧ᵗ}
            → ⟦ α₁ ⟧ᵗ≺ v
            → ⟦ `T α₁ ⟧ᵗ≺ v
  undefined : {v : 𝔼.⟦ α₁ ⟧ᵗ}
            → ⟦ `T α₁ ⟧ᵗ≺ v
  []        : ⟦ `List α₁ ⟧ᵗ≺ []
  _∷_       : {v : 𝔼.⟦ α₁ ⟧ᵗ} {vs : List 𝔼.⟦ α₁ ⟧ᵗ}
            → ⟦ `T α₁ ⟧ᵗ≺ v
            → ⟦ `T (`List α₁) ⟧ᵗ≺ vs
            → ⟦ `List α₁ ⟧ᵗ≺ v ∷ vs

-- Now we introduce a join-semilattice (≤, ⊔, ⊥) of demands (on a fixed value).
-- We do not prove any properties yet.

infix 4 ⟦_⟧[_≻_≤ᵉ_]
data ⟦_⟧[_≻_≤ᵉ_] : (α : Ty) (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧ᵗ≺ v → ⟦ α ⟧ᵗ≺ v → Type where
  false     : ⟦ `Bool ⟧[ false ≻ false ≤ᵉ false ]
  true      : ⟦ `Bool ⟧[ true  ≻ true  ≤ᵉ true  ]
  undefined : ∀ {v d}
            → ⟦ `T α₁ ⟧[ v ≻ undefined ≤ᵉ d ]
  thunk     : ∀ {v d₁ d₂}
            → ⟦ α₁ ⟧[ v ≻ d₁ ≤ᵉ d₂ ]
            → ⟦ `T α₁ ⟧[ v ≻ thunk d₁ ≤ᵉ thunk d₂ ]
  []        : ⟦ `List α₁ ⟧[ [] ≻ [] ≤ᵉ [] ]
  _∷_       : ∀ {v₁ v₂ d₁₁ d₁₂ d₂₁ d₂₂}
            → ⟦ `T α₁ ⟧[ v₁ ≻ d₁₁ ≤ᵉ d₁₂ ]
            → ⟦ `T (`List α₁) ⟧[ v₂ ≻ d₂₁ ≤ᵉ d₂₂ ]
            → ⟦ `List α₁ ⟧[ v₁ ∷ v₂ ≻ d₁₁ ∷ d₂₁ ≤ᵉ d₁₂ ∷ d₂₂ ]

infix 4 _≤ᵉ_
_≤ᵉ_ : {α : Ty} {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧ᵗ≺ v → ⟦ α ⟧ᵗ≺ v → Type
_≤ᵉ_ = ⟦ _ ⟧[ _ ≻_≤ᵉ_]

-- `d₁ ⊔ᵉ d₂` is the join of the demands `d₁` and `d₂`.
infixl 6 _⊔ᵉ_
_⊔ᵉ_ : {v : 𝔼.⟦ α ⟧ᵗ} → ⟦ α ⟧ᵗ≺ v → ⟦ α ⟧ᵗ≺ v → ⟦ α ⟧ᵗ≺ v
false       ⊔ᵉ false       = false
true        ⊔ᵉ true        = true
thunk d₁    ⊔ᵉ thunk d₂    = thunk (d₁ ⊔ᵉ d₂)
thunk d₁    ⊔ᵉ undefined   = thunk d₁
undefined   ⊔ᵉ thunk d₂    = thunk d₂
undefined   ⊔ᵉ undefined   = undefined
[]          ⊔ᵉ []          = []
(d₁₁ ∷ d₁₂) ⊔ᵉ (d₂₁ ∷ d₂₂) = d₁₁ ⊔ᵉ d₂₁ ∷ d₁₂ ⊔ᵉ d₂₂

-- `⊥⟦ α ⟧ᵗ≺ v` is the least demand in `α` on the total value `v`.
infix 4 ⊥⟦_⟧ᵗ≺_
⊥⟦_⟧ᵗ≺_ : ∀ α (v : 𝔼.⟦ α ⟧ᵗ) → ⟦ α ⟧ᵗ≺ v
⊥⟦ `Bool   ⟧ᵗ≺ false   = false
⊥⟦ `Bool   ⟧ᵗ≺ true    = true
⊥⟦ `T _    ⟧ᵗ≺ _       = undefined
⊥⟦ `List _ ⟧ᵗ≺ []      = []
⊥⟦ `List _ ⟧ᵗ≺ (_ ∷ _) = undefined ∷ undefined

-----------------------------------------------------
-- The bounded join-semilattice of demand contexts --
-----------------------------------------------------

-- A demand context on an evaluation context `γ` (itself over a typing context
-- `Γ`) assigns to each value `v` in `γ` some demand on `v`.

infix 4 ⟦_⟧≺ᶜ_
⟦_⟧≺ᶜ_ : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → Type
⟦ Γ ⟧≺ᶜ γ = All (uncurry ⟦_⟧ᵗ≺_) (All.toList γ)

infix 4 ≺ᶜ_
≺ᶜ_ : 𝔼.⟦ Γ ⟧ᶜ → Type
≺ᶜ γ = All (uncurry ⟦_⟧ᵗ≺_) (All.toList γ)

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
⊥⟦_⟧≺ᶜ_ : ∀ Γ (γ : 𝔼.⟦ Γ ⟧ᶜ) → ⟦ Γ ⟧≺ᶜ γ
⊥⟦ Γ ⟧≺ᶜ γ = All.universal (uncurry ⊥⟦_⟧ᵗ≺_) _

⊥ᶜ : ≺ᶜ γ
⊥ᶜ = ⊥⟦ _ ⟧≺ᶜ _

---------------------------------------------------------
-- The bounded join-semilattice of  --
---------------------------------------------------------

infix 4 ⌈_⌉[_≤ᵐ_]
⌈_⌉[_≤ᵐ_] : {A : Type a} → Rel A ℓ → Rel (Tick A) ℓ
⌈ _≤_ ⌉[ m₁ ≤ᵐ m₂ ] = Pointwise _≤_ ℕ._≤_ m₁ m₂

infixl 6 ⌈_⌉[_⊔ᵐ_]
⌈_⌉[_⊔ᵐ_] : Op₂ A → Op₂ (Tick A)
⌈ _⊔_ ⌉[ m₁ ⊔ᵐ m₂ ] = ×.zip _⊔_ ℕ._⊔_ m₁ m₂

⌈_⌉⊥ᵐ : {A : Type a} → A → Tick A
⌈ x ⌉⊥ᵐ = return x

infix 4 ⟦_⟧≺ᵐ_
⟦_⟧≺ᵐ_ : (Γ : Ctx) → 𝔼.⟦ Γ ⟧ᶜ → Type
⟦ Γ ⟧≺ᵐ γ = Tick (⟦ Γ ⟧≺ᶜ γ)

infix 4 ≺ᵐ_
≺ᵐ_ : 𝔼.⟦ Γ ⟧ᶜ → Type
≺ᵐ γ = ⟦ _ ⟧≺ᵐ γ

infix 4 ⟦_⟧[_≻_≤ᵐ_]
⟦_⟧[_≻_≤ᵐ_] : (Γ : Ctx) (γ : 𝔼.⟦ Γ ⟧ᶜ) → ⟦ Γ ⟧≺ᵐ γ → ⟦ Γ ⟧≺ᵐ γ → Type
⟦ Γ ⟧[ γ ≻ m₁ ≤ᵐ m₂ ] = ⌈ _≤ᶜ_ ⌉[ m₁ ≤ᵐ m₂ ]

infix 4 _≤ᵐ_
_≤ᵐ_ : ≺ᵐ γ → ≺ᵐ γ → Type
_≤ᵐ_ = ⟦ _ ⟧[ _ ≻_≤ᵐ_]

infixl 6 _⊔ᵐ_
_⊔ᵐ_ : ≺ᵐ γ → ≺ᵐ γ → ≺ᵐ γ
_⊔ᵐ_ = ×.zip _⊔ᶜ_ ℕ._⊔_

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
  ⟦ α ⟧ᵗ≺ 𝔼.⟦ t ⟧ᵉ γ →
  ≺ᵐ γ

⟦if_,_⟧ᵉ :
  (t₂ t₃ : Γ ⊢ α)
  (γ : 𝔼.⟦ Γ ⟧ᶜ)
  (v : Bool) →
  ⟦ α ⟧ᵗ≺ 𝔼.⟦if t₂ , t₃ ⟧ᵉ γ v →
  ⟦ Γ ⸴ `Bool ⟧≺ᵐ (γ ⸴ v)

⟦foldr_,_⟧ᵉ :
  (t₁ : Γ ⸴ `T α₁ ⸴ `T α₂ ⊢ α₂) →
  (t₂ : Γ ⊢ α₂) →
  (γ : 𝔼.⟦ Γ ⟧ᶜ) →
  (xs : List 𝔼.⟦ α₁ ⟧ᵗ) →
  ⟦ α₂ ⟧ᵗ≺ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ xs →
  ⟦ Γ ⸴ `List α₁ ⟧≺ᵐ (γ ⸴ xs)

⟦if′_⟧ᵉ : (t₁ : Γ ⊢ `Bool)
          (γ : 𝔼.⟦ Γ ⟧ᶜ)
        → ⟦ Γ ⸴ `Bool ⟧≺ᶜ (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ)
        → ≺ᵐ γ
⟦if′ t₁ ⟧ᵉ γ (δ ⸴ d₁) = do
  δ′ ← ⟦ t₁ ⟧ᵉ γ d₁
  return (δ′ ⊔ᶜ δ)

⟦ ` x                      ⟧ᵉ γ d         = return (⊥ᶜ [ ∈ᴸ⇒lookup∈ᴸtoList x ]≔ d)
⟦ `let t₁ `in t₂           ⟧ᵉ γ d₂        = do
  d₁ ∷ γ₂′    ← ⟦ t₂ ⟧ᵉ (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ) d₂
  γ₁′         ← ⟦ t₁ ⟧ᵉ γ d₁
  return (γ₁′ ⊔ᶜ γ₂′)
⟦ `false                   ⟧ᵉ γ d         = ⊥ᵐ
⟦ `true                    ⟧ᵉ γ d         = ⊥ᵐ
⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ d₂₃       =
  ⟦if t₂ , t₃ ⟧ᵉ γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₂₃ >>= ⟦if′ t₁ ⟧ᵉ γ
⟦ `[]                      ⟧ᵉ γ d         = ⊥ᵐ
⟦ t₁ `∷ t₂                 ⟧ᵉ γ (d₁ ∷ d₂) = ⟦ t₁ ⟧ᵉ γ d₁ ⊔ᵐ ⟦ t₂ ⟧ᵉ γ d₂
⟦ `foldr t₁ t₂ t₃          ⟧ᵉ γ d₁₂       = do
  (γ₁₂′ ⸴ d₃) ← ⟦foldr t₁ , t₂ ⟧ᵉ γ (𝔼.⟦ t₃ ⟧ᵉ γ) d₁₂
  γ₃′         ← ⟦ t₃ ⟧ᵉ γ d₃
  return (γ₁₂′ ⊔ᶜ γ₃′)
⟦ `tick t                  ⟧ᵉ γ d         = do
  tick
  ⟦ t ⟧ᵉ γ d
⟦ `lazy t                  ⟧ᵉ γ (thunk d) = ⟦ t ⟧ᵉ γ d
⟦ `lazy t₁                 ⟧ᵉ γ undefined = ⊥ᵐ
⟦ `force t₁                ⟧ᵉ γ d         = ⟦ t₁ ⟧ᵉ γ (thunk d)

⟦if t₂ , t₃ ⟧ᵉ γ false d = do
  γ′ ← ⟦ t₃ ⟧ᵉ γ d
  return (γ′ ⸴ false)
⟦if t₂ , t₃ ⟧ᵉ γ true  d = do
  γ′ ← ⟦ t₂ ⟧ᵉ γ d
  return (γ′ ⸴ true)

⟦foldr′_,_⟧ᵉ : ∀ {Γ α β}
  (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) →
  (t₂ : Γ ⊢ β) →
  (γ : 𝔼.⟦ Γ ⟧ᶜ) →
  (xs : List 𝔼.⟦ α ⟧ᵗ) →
  ⟦ `T β ⟧ᵗ≺ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ xs →
  Tick (≺ᶜ γ × ⟦ `T (`List α) ⟧ᵗ≺ xs)

⟦foldr t₁ , t₂ ⟧ᵉ γ []       d = do
  γ′           ← ⟦ t₂ ⟧ᵉ γ d
  return (γ′ ⸴ [])
⟦foldr t₁ , t₂ ⟧ᵉ γ (x ∷ xs) d = do
  γ′ ⸴ a′ ⸴ b′ ← ⟦ t₁ ⟧ᵉ (γ ⸴ x ⸴ 𝔼.⟦foldr t₁ , t₂ ⟧ᵉ γ xs) d
  γ′′ , d′     ← ⟦foldr′ t₁ , t₂ ⟧ᵉ γ xs b′
  return (γ′ ⊔ᶜ γ′′ ⸴ a′ ∷ d′)

⟦foldr′ t₁ , t₂ ⟧ᵉ γ xs undefined = return (⊥ᶜ , undefined)
⟦foldr′ t₁ , t₂ ⟧ᵉ γ xs (thunk d) = do
  γ′ ⸴ d′ ← ⟦foldr t₁ , t₂ ⟧ᵉ γ xs d
  return (γ′ , thunk d′)

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

⊥ᵉ-minimum : ∀ {v} → Minimum ⟦ α ⟧[ v ≻_≤ᵉ_] (⊥⟦ α ⟧ᵗ≺ v)
⊥ᵉ-minimum false      = false
⊥ᵉ-minimum true       = true
⊥ᵉ-minimum (thunk d₁) = undefined
⊥ᵉ-minimum undefined  = undefined
⊥ᵉ-minimum []         = []
⊥ᵉ-minimum (d₁ ∷ d₂)  = undefined ∷ undefined

≤ᵉ-⊔ᵉ-⊥ᵉ-isBoundedJoinSemilattice : ∀ {v} → IsBoundedJoinSemilattice _≡_ ⟦ α ⟧[ v ≻_≤ᵉ_] _⊔ᵉ_ (⊥⟦ α ⟧ᵗ≺ v)
≤ᵉ-⊔ᵉ-⊥ᵉ-isBoundedJoinSemilattice = record
  { isJoinSemilattice = ≤ᵉ-⊔ᵉ-isJoinSemilattice
  ; minimum           = ⊥ᵉ-minimum
  }

---------------------------------------
-- Ditto the above, but for contexts --
---------------------------------------

≤ᶜ-refl : Reflexive ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-refl = AllPointwise.reflexive ≤ᵉ-refl

≤ᶜ-trans : Transitive ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-trans = AllPointwise.transitive ≤ᵉ-trans

≤ᶜ-isPreorder : IsPreorder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-isPreorder {Γ = Γ} = {!AllPointwise.isPreorder ?!}

≤ᶜ-antisym : Antisymmetric _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-antisym = AllPointwise.antisymmetric ≤ᵉ-antisym

≤ᶜ-isPartialOrder : IsPartialOrder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
≤ᶜ-isPartialOrder = record
  { isPreorder = ≤ᶜ-isPreorder
  ; antisym    = ≤ᶜ-antisym
  }

δ₁≤ᶜδ₁⊔ᶜδ₂ : ∀ δ₁ δ₂ → ⟦ Γ ⟧[ γ ≻ δ₁ ≤ᶜ δ₁ ⊔ᶜ δ₂ ]
δ₁≤ᶜδ₁⊔ᶜδ₂ {γ = []   } []        []        = []
δ₁≤ᶜδ₁⊔ᶜδ₂ {γ = γ ⸴ v} (δ₁ ⸴ d₁) (δ₂ ⸴ d₂) = δ₁≤ᶜδ₁⊔ᶜδ₂ δ₁ δ₂ ⸴ d₁≤ᵉd₁⊔ᵉd₂ d₁ d₂

δ₂≤ᶜδ₁⊔ᶜδ₂ : ∀ δ₁ δ₂ → ⟦ Γ ⟧[ γ ≻ δ₂ ≤ᶜ δ₁ ⊔ᶜ δ₂ ]
δ₂≤ᶜδ₁⊔ᶜδ₂ {γ = []   } []        []        = []
δ₂≤ᶜδ₁⊔ᶜδ₂ {γ = γ ⸴ v} (δ₁ ⸴ d₁) (δ₂ ⸴ d₂) = δ₂≤ᶜδ₁⊔ᶜδ₂ δ₁ δ₂ ⸴ d₂≤ᵉd₁⊔ᵉd₂ d₁ d₂

⊔ᶜ-least :
  ⟦ Γ ⟧[ γ ≻ δ₁ ≤ᶜ δ₃ ] →
  ⟦ Γ ⟧[ γ ≻ δ₂ ≤ᶜ δ₃ ] →
  ⟦ Γ ⟧[ γ ≻ δ₁ ⊔ᶜ δ₂ ≤ᶜ δ₃ ]
⊔ᶜ-least {γ = []   } []              []              = []
⊔ᶜ-least {γ = γ ⸴ v} (δ₁≤δ₃ ⸴ d₁≤d₃) (δ₂≤δ₃ ⸴ d₂≤d₃) = ⊔ᶜ-least δ₁≤δ₃ δ₂≤δ₃ ⸴ ⊔ᵉ-least d₁≤d₃ d₂≤d₃

⊔ᶜ-supremum : Supremum ⟦ Γ ⟧[ γ ≻_≤ᶜ_] _⊔ᶜ_
⊔ᶜ-supremum δ₁ δ₂ = δ₁≤ᶜδ₁⊔ᶜδ₂ δ₁ δ₂ , δ₂≤ᶜδ₁⊔ᶜδ₂ δ₁ δ₂ , λ _ → ⊔ᶜ-least

≤ᶜ-⊔ᶜ-isJoinSemilattice : IsJoinSemilattice _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] _⊔ᶜ_
≤ᶜ-⊔ᶜ-isJoinSemilattice = record
  { isPartialOrder = ≤ᶜ-isPartialOrder
  ; supremum       = ⊔ᶜ-supremum
  }

≤ᶜ-⊔ᶜ-JoinSemilattice : 𝔼.⟦ Γ ⟧ᶜ → JoinSemilattice _ _ _
≤ᶜ-⊔ᶜ-JoinSemilattice γ = record
  { Carrier           = ≺ᶜ γ
  ; _≈_               = _≡_
  ; _≤_               = _≤ᶜ_
  ; _∨_               = _⊔ᶜ_
  ; isJoinSemilattice = ≤ᶜ-⊔ᶜ-isJoinSemilattice
  }

⊔ᶜ-monotonic : _⊔ᶜ_ Preserves₂ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᶜ_]
⊔ᶜ-monotonic = Relation.Binary.Lattice.Properties.JoinSemilattice.∨-monotonic (≤ᶜ-⊔ᶜ-JoinSemilattice _)

⊥ᶜ-minimum : Minimum ⟦ Γ ⟧[ γ ≻_≤ᶜ_] (⊥⟦ Γ ⟧≺ᶜ γ)
⊥ᶜ-minimum {γ = []   } []      = []
⊥ᶜ-minimum {γ = γ ⸴ v} (δ ⸴ d) = ⊥ᶜ-minimum δ ⸴ ⊥ᵉ-minimum d

-- ≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≡_ ⟦ Γ ⟧[ γ ≻_≤ᶜ_] _⊔ᶜ_ (⊥⟦ Γ ⟧≺ᶜ γ)
-- ≤ᶜ-⊔ᶜ-⊥ᶜ-isBoundedJoinSemilattice = record
--   { isJoinSemilattice = ≤ᶜ-⊔ᶜ-isJoinSemilattice
--   ; minimum           = ⊥ᶜ-minimum
--   }

--------------------------------------------------
-- Ditto the above, but for contexts with costs --
--------------------------------------------------

≤ᵐ-refl : Reflexive ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-refl = ≤ᶜ-refl , ≤-refl

≤ᵐ-trans : Transitive ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-trans (δ₁≤δ₂ , c₁≤c₂) (δ₂≤δ₃ , c₂≤c₃) = ≤ᶜ-trans δ₁≤δ₂ δ₂≤δ₃ , ≤-trans c₁≤c₂ c₂≤c₃

≤ᵐ-isPreorder : IsPreorder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-isPreorder = record
  { isEquivalence = ≡.isEquivalence
  ; reflexive     = λ{ refl → ≤ᵐ-refl }
  ; trans         = ≤ᵐ-trans
  }

≤ᵐ-antisym : Antisymmetric _≡_ ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-antisym (δ₁≤δ₂ , c₁≤c₂)(δ₂≤δ₁ , c₂≤c₁) = ×-≡,≡→≡ (≤ᶜ-antisym δ₁≤δ₂ δ₂≤δ₁ , ≤-antisym c₁≤c₂ c₂≤c₁)

≤ᵐ-isPartialOrder : IsPartialOrder _≡_ ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
≤ᵐ-isPartialOrder = record
  { isPreorder = ≤ᵐ-isPreorder
  ; antisym    = ≤ᵐ-antisym
  }

m₁≤ᵐm₁⊔ᵐm₂ : ∀ m₁ m₂ → ⟦ Γ ⟧[ γ ≻ m₁ ≤ᵐ m₁ ⊔ᵐ m₂ ]
m₁≤ᵐm₁⊔ᵐm₂ (δ₁ , c₁) (δ₂ , c₂) = δ₁≤ᶜδ₁⊔ᶜδ₂ δ₁ δ₂ , m≤m⊔n c₁ c₂

m₂≤ᵐm₁⊔ᵐm₂ : ∀ m₁ m₂ → ⟦ Γ ⟧[ γ ≻ m₂ ≤ᵐ m₁ ⊔ᵐ m₂ ]
m₂≤ᵐm₁⊔ᵐm₂ (δ₁ , c₁) (δ₂ , c₂) = δ₂≤ᶜδ₁⊔ᶜδ₂ δ₁ δ₂ , m≤n⊔m c₁ c₂

⊔ᵐ-least : ∀ {m₁ m₂ m₃} →
  ⟦ Γ ⟧[ γ ≻ m₁ ≤ᵐ m₃ ] →
  ⟦ Γ ⟧[ γ ≻ m₂ ≤ᵐ m₃ ] →
  ⟦ Γ ⟧[ γ ≻ m₁ ⊔ᵐ m₂ ≤ᵐ m₃ ]
⊔ᵐ-least (δ₁≤δ₃ , c₁≤c₃) (δ₂≤δ₃ , c₂≤c₃) = ⊔ᶜ-least δ₁≤δ₃ δ₂≤δ₃ , ⊔-lub c₁≤c₃ c₂≤c₃

⊔ᵐ-supremum : Supremum ⟦ Γ ⟧[ γ ≻_≤ᵐ_] _⊔ᵐ_
⊔ᵐ-supremum m₁ m₂ = m₁≤ᵐm₁⊔ᵐm₂ m₁ m₂ , m₂≤ᵐm₁⊔ᵐm₂ m₁ m₂ , λ _ → ⊔ᵐ-least

≤ᵐ-⊔ᵐ-isJoinSemilattice : IsJoinSemilattice _≡_ ⟦ Γ ⟧[ γ ≻_≤ᵐ_] _⊔ᵐ_
≤ᵐ-⊔ᵐ-isJoinSemilattice = record
  { isPartialOrder = ≤ᵐ-isPartialOrder
  ; supremum       = ⊔ᵐ-supremum
  }

≤ᵐ-⊔ᵐ-JoinSemilattice : 𝔼.⟦ Γ ⟧ᶜ → JoinSemilattice _ _ _
≤ᵐ-⊔ᵐ-JoinSemilattice γ = record
  { Carrier           = ≺ᵐ γ
  ; _≈_               = _≡_
  ; _≤_               = _≤ᵐ_
  ; _∨_               = _⊔ᵐ_
  ; isJoinSemilattice = ≤ᵐ-⊔ᵐ-isJoinSemilattice
  }

⊔ᵐ-monotonic : _⊔ᵐ_ Preserves₂ ⟦ Γ ⟧[ γ ≻_≤ᵐ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᵐ_] ⟶ ⟦ Γ ⟧[ γ ≻_≤ᵐ_]
⊔ᵐ-monotonic = Relation.Binary.Lattice.Properties.JoinSemilattice.∨-monotonic (≤ᵐ-⊔ᵐ-JoinSemilattice _)

⊥ᵐ-minimum : Minimum ⟦ Γ ⟧[ γ ≻_≤ᵐ_] (⊥⟦ Γ ⟧≺ᵐ γ)
⊥ᵐ-minimum (δ , c) = ⊥ᶜ-minimum δ , z≤n

≤ᵐ-⊔ᵐ-⊥ᵐ-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≡_ ⟦ Γ ⟧[ γ ≻_≤ᵐ_] _⊔ᵐ_ (⊥⟦ Γ ⟧≺ᵐ γ)
≤ᵐ-⊔ᵐ-⊥ᵐ-isBoundedJoinSemilattice = record
  { isJoinSemilattice = ≤ᵐ-⊔ᵐ-isJoinSemilattice
  ; minimum           = ⊥ᵐ-minimum
  }

>>=-mono : {γ₁ : 𝔼.⟦ Γ₁ ⟧ᶜ} {γ₂ : 𝔼.⟦ Γ₂ ⟧ᶜ}
           {m₁ m₂ : ⟦ Γ₁ ⟧≺ᵐ γ₁} {k₁ k₂ : ≺ᶜ γ₁ → ≺ᵐ γ₂}
         → m₁ ≤ᵐ m₂
         → (∀ {δ₁ δ₂} → δ₁ ≤ᶜ δ₂ → k₁ δ₁ ≤ᵐ k₂ δ₂)
         → (m₁ >>= k₁) ≤ᵐ (m₂ >>= k₂)
>>=-mono (p₁ , p₂) q = proj₁ (q p₁) , +-mono-≤ p₂ (proj₂ (q p₁))

>>=-monoˡ : {γ₁ : 𝔼.⟦ Γ₁ ⟧ᶜ} {γ₂ : 𝔼.⟦ Γ₂ ⟧ᶜ}
            {m₁ m₂ : ⟦ Γ₁ ⟧≺ᵐ γ₁}
            (k : ≺ᶜ γ₁ → ≺ᵐ γ₂)
          → m₁ ≤ᵐ m₂
          → (∀ {δ₁ δ₂} → δ₁ ≤ᶜ δ₂ → k δ₁ ≤ᵐ k δ₂)
          → (m₁ >>= k) ≤ᵐ (m₂ >>= k)
>>=-monoˡ _ = >>=-mono

return-mono : {δ₁ δ₂ : ⟦ Γ₁ ⟧≺ᶜ γ}
            → δ₁ ≤ᶜ δ₂
            → return δ₁ ≤ᵐ return δ₂
return-mono δ₁≤δ₂ = δ₁≤δ₂ , ≤-refl

--------------------------------------
-- Monotonicity of demand semantics --
--------------------------------------

-- ⟦ `let t₁ `in t₂           ⟧ᵉ γ d₂        = do
--   d₁ ∷ γ₂′    ← ⟦ t₂ ⟧ᵉ (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ) d₂
--   γ₁′         ← ⟦ t₁ ⟧ᵉ γ d₁
--   return (γ₁′ ⊔ᶜ γ₂′)

⟦_⟧ᵉ-mono : (t : Γ ⊢ α)
            (γ : 𝔼.⟦ Γ ⟧ᶜ)
            {d₁ d₂ : ⟦ α ⟧ᵗ≺ 𝔼.⟦ t ⟧ᵉ γ}
          → d₁ ≤ᵉ d₂
          → ⟦ t ⟧ᵉ γ d₁ ≤ᵐ ⟦ t ⟧ᵉ γ d₂

⟦if_,_⟧ᵉ-mono :
  (t₂ t₃ : Γ ⊢ α)
  (γ : 𝔼.⟦ Γ ⟧ᶜ)
  (v : Bool)
  {d₂ d₃ : ⟦ α ⟧ᵗ≺ 𝔼.⟦if t₂ , t₃ ⟧ᵉ γ v} →
  d₂ ≤ᵉ d₃ →
  ⟦if t₂ , t₃ ⟧ᵉ γ v d₂ ≤ᵐ ⟦if t₂ , t₃ ⟧ᵉ γ v d₃
⟦if t₂ , t₃ ⟧ᵉ-mono γ false d₂≤d₃
  = {!!}
  -- = (⟦ t₃ ⟧ᵉ-mono γ d₂≤d₃ .proj₁ , false) ,
  --   subst₂ _≤_ (sym (+-identityʳ (⟦ t₃ ⟧ᵉ γ _ .proj₂))) (sym (+-identityʳ (⟦ t₃ ⟧ᵉ γ _ .proj₂))) (⟦ t₃ ⟧ᵉ-mono γ d₂≤d₃ .proj₂)
⟦if t₂ , t₃ ⟧ᵉ-mono γ true d₂≤d₃
  = {!!}
  -- = (⟦ t₂ ⟧ᵉ-mono γ d₂≤d₃ .proj₁ , true) ,
  --   subst₂ _≤_ (sym (+-identityʳ (⟦ t₂ ⟧ᵉ γ _ .proj₂))) (sym (+-identityʳ (⟦ t₂ ⟧ᵉ γ _ .proj₂))) (⟦ t₂ ⟧ᵉ-mono γ d₂≤d₃ .proj₂)

import Effect.Applicative
import Effect.Monad
⟦ ` x                      ⟧ᵉ-mono γ d₁≤d₂ =
  {!!}
  -- return-mono (AllPointwise.updateAt (∈ᴸ⇒lookup∈ᴸtoList x) (const d₁≤d₂) ≤ᶜ-refl)
⟦ `let t₁ `in t₂           ⟧ᵉ-mono γ d₁≤d₂ = {!!}
  -- >>=-mono (⟦ t₂        ⟧ᵉ-mono (γ ⸴ 𝔼.⟦ t₁ ⟧ᵉ γ) d₁≤d₂) {!!}
⟦ `false                   ⟧ᵉ-mono γ d₁≤d₂ = ≤ᵐ-refl -- ≤ᵐ-refl
⟦ `true                    ⟧ᵉ-mono γ d₁≤d₂ = ≤ᵐ-refl

  -- γ₂₃′ ⸴ d₂   ← ⟦if t₂ , t₃ ⟧ᵉ γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₂₃
  -- γ₁′         ← ⟦ t₁ ⟧ᵉ γ d₂
  -- return (γ₁′ ⊔ᶜ γ₂₃′)
⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ-mono γ {d₁ = d₁} {d₂ = d₂} d₁≤d₂ =
  >>=-monoˡ
    (⟦if′ t₁ ⟧ᵉ γ)
    (⟦if t₂ , t₃ ⟧ᵉ-mono γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₁≤d₂)
    (λ{ (φ₁ ⸴ φ₂) → {!>>=-monoˡ ? ? ?!} })
  -- >>=-monoˡ
  -- {k = λ{ (x ⸴ y) → {!!} }}
  -- (⟦if t₂ , t₃ ⟧ᵉ-mono γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₁≤d₂)
  -- λ{ (φ₁ ⸴ φ₂) → >>=-monoˡ (⟦ t₁ ⟧ᵉ-mono γ φ₂) (λ ψ → {!!}) }
  -- (λ{ (φ₁ ⸴ φ₂) → >>=-mono (⟦ t₁ ⟧ᵉ-mono γ φ₂)
  --   (λ ψ → return-mono (⊔ᶜ-monotonic ψ φ₁)) })

{-
>>=-mono (⟦if t₂ , t₃ ⟧ᵉ-mono γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₁≤d₂)
  (λ{ (φ₁ ⸴ φ₂) → >>=-mono (⟦ t₁ ⟧ᵉ-mono γ φ₂)
    (λ ψ → return-mono (⊔ᵐ-monotonic ψ φ₁)) })
-}

-- {k₁ = λ{ (γ₂₃′ ⸴ d₂) → ⟦ t₁ ⟧ᵉ γ d₂ >>= (λ γ₁′ → return (γ₁′ ⊔ᶜ γ₂₃′))}} {k₂ = λ{(γ₂₃′ ⸴ d₂) → ⟦ t₁ ⟧ᵉ γ d₂ >>= (λ γ₁′ → return (γ₁′ ⊔ᶜ γ₂₃′))}}
-- {m₁ = ⟦if t₂ , t₃ ⟧ᵉ γ (𝔼.⟦ t₁ ⟧ᵉ γ) d₁}
-- ... | p = ?
-- = {!!}
⟦ `[]                      ⟧ᵉ-mono γ d₁≤d₂ = ≤ᵐ-refl
⟦ t₁ `∷ t₂                 ⟧ᵉ-mono γ (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) =
  ⊔ᵐ-monotonic (⟦ t₁ ⟧ᵉ-mono γ d₁₁≤d₂₁) (⟦ t₂ ⟧ᵉ-mono γ d₁₂≤d₂₂)
⟦ `foldr t₁ t₂ t₃          ⟧ᵉ-mono γ d₁≤d₂ = {!!}
⟦ `tick t₁                 ⟧ᵉ-mono γ d₁≤d₂ =
  let (φ , ψ) = ⟦ t₁ ⟧ᵉ-mono γ d₁≤d₂
  in φ , s≤s ψ
⟦ `lazy t₁                 ⟧ᵉ-mono γ undefined = ⊥ᵐ-minimum _
⟦ `lazy t₁                 ⟧ᵉ-mono γ (thunk d₁≤d₂) = ⟦ t₁ ⟧ᵉ-mono γ d₁≤d₂
⟦ `force t₁                ⟧ᵉ-mono γ d₁≤d₂ = ⟦ t₁ ⟧ᵉ-mono γ (thunk d₁≤d₂)
