module LogicalLaziness.Language.Explicit where

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

Tm = _⊢_
