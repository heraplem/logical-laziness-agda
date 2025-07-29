module Explicit where

open import Agda.Primitive using () renaming (Set to Type; Setω to Typeω)
open import Data.Bool
  hiding (T)
open import Relation.Binary.PropositionalEquality
open import Algebra.Bundles.Raw
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Effect.Monad.Identity
open import Effect.Monad.Writer
open import Effect.Monad.Writer.Transformer
open import Data.Product
  hiding (_<*>_)
open import Data.Nat
  hiding (_⊔_)
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Membership.Propositional

open import Core

{-

Mnemonics:

- ty—  has to do with types
- ctx— has to do with contexts
- tm—  has to do with terms
- —ₑ   has to do with forward evaluation
- —ₐ   has to do with backwards evaluation

-}

data ty : Type where
  `Bool : ty
  `T    : ty → ty
  `List : ty → ty

variable
  τ α β : ty

ctx : Type
ctx = List ty

variable
  Γ : ctx

infix 4 _⊢_
infix 1 `if_`then_`else_
data _⊢_ : ctx → ty → Type where
  `_               : τ ∈ Γ
                   → Γ ⊢ τ

  `let_`in_        : Γ ⊢ α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β

  `false           : Γ ⊢ `Bool
  `true            : Γ ⊢ `Bool

  `if_`then_`else_ : Γ ⊢ `Bool
                   → Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ τ

  `[]              : Γ ⊢ `List τ

  _`∷_             : Γ ⊢ `T τ
                   → Γ ⊢ `T (`List τ)
                   → Γ ⊢ `List τ

  `foldr           : Γ ⸴ `T α ⸴ `T β ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ `List α → Γ ⊢ β

  `tick            : Γ ⊢ τ
                   → Γ ⊢ τ

  `lazy            : Γ ⊢ τ
                   → Γ ⊢ `T τ

  `force           : Γ ⊢ `T τ
                   → Γ ⊢ τ

tm = _⊢_

ty⟦_⟧ₑ : ty → Type
ty⟦ `Bool ⟧ₑ   = Bool
ty⟦ `T τ ⟧ₑ    = ty⟦ τ ⟧ₑ
ty⟦ `List τ ⟧ₑ = List ty⟦ τ ⟧ₑ

ctx⟦_⟧ₑ : ctx → Type
ctx⟦_⟧ₑ = All ty⟦_⟧ₑ

tm⟦_⟧ₑ : Γ ⊢ τ → ctx⟦ Γ ⟧ₑ → ty⟦ τ ⟧ₑ

foldr⟦_,_⟧ₑ : Γ ⸴ `T α ⸴ `T β ⊢ β
            → Γ ⊢ β
            → ctx⟦ Γ ⟧ₑ
            → List ty⟦ α ⟧ₑ
            → ty⟦ β ⟧ₑ

tm⟦ ` x ⟧ₑ                      g = All.lookup g x
tm⟦ `let t₁ `in t₂ ⟧ₑ           g = let a = tm⟦ t₁ ⟧ₑ g in tm⟦ t₂ ⟧ₑ (g ⸴ a)
tm⟦ `false ⟧ₑ                   g = false
tm⟦ `true ⟧ₑ                    g = true
tm⟦ `if t₁ `then t₂ `else t₃ ⟧ₑ g = if tm⟦ t₁ ⟧ₑ g then tm⟦ t₂ ⟧ₑ g else tm⟦ t₃ ⟧ₑ g
tm⟦ `[] ⟧ₑ                      g = []
tm⟦ t₁ `∷ t₂ ⟧ₑ                 g = tm⟦ t₁ ⟧ₑ g ∷ tm⟦ t₂ ⟧ₑ g
tm⟦ `foldr t₁ t₂ t₃ ⟧ₑ          g = foldr⟦ t₁ , t₂ ⟧ₑ g (tm⟦ t₃ ⟧ₑ g)
tm⟦ `tick t₁ ⟧ₑ                 g = tm⟦ t₁ ⟧ₑ g
tm⟦ `lazy t₁ ⟧ₑ                 g = tm⟦ t₁ ⟧ₑ g
tm⟦ `force t₁ ⟧ₑ                g = tm⟦ t₁ ⟧ₑ g

foldr⟦ t₁ , t₂ ⟧ₑ g = foldr (λ a b → tm⟦ t₁ ⟧ₑ (g ⸴ a ⸴ b)) (tm⟦ t₂ ⟧ₑ g)

-- `ty⟦ τ ⟧ₐ≺ v` describes the set of partial values in `τ` that approximate the
-- total value `v`.
infix 4 ty⟦_⟧ₐ≺_
data ty⟦_⟧ₐ≺_ : (α : ty) → ty⟦ α ⟧ₑ → Type where
  ↓Bool      : {v : Bool} → ty⟦ `Bool ⟧ₐ≺ v
  ↓thunk     : {α : ty} {v : ty⟦ α ⟧ₑ} → ty⟦ α ⟧ₐ≺ v → ty⟦ `T α ⟧ₐ≺ v
  ↓undefined : {α : ty} {v : ty⟦ α ⟧ₑ} → ty⟦ `T α ⟧ₐ≺ v
  ↓[]        : {α : ty} → ty⟦ `List α ⟧ₐ≺ []
  _↓∷_       : {α : ty} {v : ty⟦ α ⟧ₑ} {vs : List ty⟦ α ⟧ₑ} →
    ty⟦ `T α ⟧ₐ≺ v → ty⟦ `T (`List α) ⟧ₐ≺ vs →
    ty⟦ `List α ⟧ₐ≺ v ∷ vs

-- `↓ctx g` is the set of contexts that elementwise approximate `g`.
↓ctx : ∀ {Γ} → ctx⟦ Γ ⟧ₑ → Type
↓ctx g = All (uncurry ty⟦_⟧ₐ≺_) (All.toList g)

-- Least upper bounds of approximations.
lub : {α : ty} {v : ty⟦ α ⟧ₑ} → ty⟦ α ⟧ₐ≺ v → ty⟦ α ⟧ₐ≺ v → ty⟦ α ⟧ₐ≺ v
lub ↓Bool      ↓Bool      = ↓Bool
lub (↓thunk x) (↓thunk y) = ↓thunk (lub x y)
lub (↓thunk x) ↓undefined = ↓thunk x
lub ↓undefined (↓thunk y) = ↓thunk y
lub ↓undefined ↓undefined = ↓undefined
lub ↓[]        ↓[]        = ↓[]
lub (x ↓∷ x₁) (y ↓∷ y₁)   = lub x y ↓∷ lub x₁ y₁

-- Pairwise joins of approximation contexts.
_ctx⊔_ : ∀ {Γ} {g : ctx⟦ Γ ⟧ₑ} → ↓ctx g → ↓ctx g → ↓ctx g
bs₁ ctx⊔ bs₂ = All.zipWith (uncurry lub) (bs₁ , bs₂)

-- Least approximation of a total value.
⊥ : ∀ τ (v : ty⟦ τ ⟧ₑ) → ty⟦ τ ⟧ₐ≺ v
⊥ `Bool     _       = ↓Bool
⊥ (`T _)    _       = ↓undefined
⊥ (`List _) []      = ↓[]
⊥ (`List _) (_ ∷ _) = ↓undefined ↓∷ ↓undefined

-- Least approximation of a total evaluation context.
⊥ctx : ∀ {Γ} {g : ctx⟦ Γ ⟧ₑ} → ↓ctx g
⊥ctx = universal (uncurry ⊥) _

M : Type → Type
M = Writer +-0-rawMonoid

_⊔_ : ∀ {Γ} {g : ctx⟦ Γ ⟧ₑ} → M (↓ctx g) → M (↓ctx g) → M (↓ctx g)
m₁ ⊔ m₂ = _ctx⊔_ <$> m₁ <*> m₂

---------------------------
-- Backwards evaluation. --
---------------------------

↓tm : ∀ {Γ} {g : ctx⟦ Γ ⟧ₑ} {τ : ty}
  (t : Γ ⊢ τ) →
  ty⟦ τ ⟧ₐ≺ tm⟦ t ⟧ₑ g
  → M (↓ctx g)

foldrD : ∀ {Γ α β}
  {g : ctx⟦ Γ ⟧ₑ} →
  (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) →
  (t₂ : Γ ⊢ β) →
  (xs : List ty⟦ α ⟧ₑ) →
  ty⟦ β ⟧ₐ≺ foldr⟦ t₁ , t₂ ⟧ₑ g xs →
  M (↓ctx g × ty⟦ `List α ⟧ₐ≺ xs)
foldrD′ : ∀ {Γ α β}
  {g : ctx⟦ Γ ⟧ₑ} →
  (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) →
  (t₂ : Γ ⊢ β) →
  (xs : List ty⟦ α ⟧ₑ) →
  ty⟦ `T β ⟧ₐ≺ foldr⟦ t₁ , t₂ ⟧ₑ g xs →
  M (↓ctx g × ty⟦ `T (`List α) ⟧ₐ≺ xs)

↓tm (` x) a = return (⊥ctx [ ∈⇒lookup∈toList x ]≔ a)
↓tm (`let t₁ `in t₂) a₂ = do
  a₁ ∷ d₂ ← ↓tm t₂ a₂
  d₁ ← ↓tm t₁ a₁
  pure (d₁ ctx⊔ d₂)
↓tm `false _ = return ⊥ctx
↓tm `true _ = return ⊥ctx
↓tm {g = g} (`if t₁ `then t₂ `else t₃) a = ↓tm t₁ ↓Bool ⊔ d where
  d : M (↓ctx g)
  d with tm⟦ t₁ ⟧ₑ g
  ... | false = ↓tm t₃ a
  ... | true = ↓tm t₂ a
↓tm `[] _ = return ⊥ctx
↓tm (t₁ `∷ t₂) (a₁ ↓∷ a₂) = ↓tm t₁ a₁ ⊔ ↓tm t₂ a₂
↓tm {g = g} (`foldr t₁ t₂ t₃) a = do
  (g′ , xs′) ← foldrD t₁ t₂ (tm⟦ t₃ ⟧ₑ g) a
  g′′ ← ↓tm t₃ xs′
  return (g′ ctx⊔ g′′)
↓tm (`tick t) a = ↓tm t a
↓tm (`lazy t) (↓thunk a) = ↓tm t a
↓tm (`lazy t) ↓undefined = return ⊥ctx
↓tm (`force t) a = ↓tm t (↓thunk a)

foldrD t₁ t₂ [] d = do
  d′ ← ↓tm t₂ d
  return (d′ , ↓[])
foldrD t₁ t₂ (x ∷ xs) d = do
  g′ ⸴ a′ ⸴ b′ ← ↓tm t₁ d
  g′′ , d′ ← foldrD′ t₁ t₂ xs b′
  return (g′ ctx⊔ g′′ , a′ ↓∷ d′)

foldrD′ t₁ t₂ xs (↓thunk d) = do
  g′ , d′ ← foldrD t₁ t₂ xs d
  return (g′ , ↓thunk d′)
foldrD′ t₁ t₂ xs ↓undefined = return (⊥ctx , ↓undefined)
