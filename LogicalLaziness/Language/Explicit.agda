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
    α β : Ty

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

  _`∷_             : Γ ⊢ α
                   → Γ ⊢ `T (`List α)
                   → Γ ⊢ `List α

  `foldr           : Γ ⸴ α ⸴ `T β ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ `List α
                   → Γ ⊢ β

  `tick            : Γ ⊢ α
                   → Γ ⊢ α

  `lazy            : Γ ⊢ α
                   → Γ ⊢ `T α

  `force           : Γ ⊢ `T α
                   → Γ ⊢ α

Tm = _⊢_
