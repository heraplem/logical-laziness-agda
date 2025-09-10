module LogicalLaziness.Base where

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List
  as List
  using ( List
        ; []
        ; _∷_
        )
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any

open import LogicalLaziness.Base.Core
  public
open import LogicalLaziness.Base.Data.List.All.Relation.Binary.Pointwise
  using (_∷_)

private
  variable
    x y : A
    xs : List A
    px : P x
    pxs : All P xs

of-type : (A : Type a) → A → A
of-type A x = x
-- XXX This is codepoint #x2236.
infix 0 of-type
syntax of-type A x = x ∶ A

infix 4 _∋_
_∋_ : (A → Type ℓ) → A → Type ℓ
P ∋ x = P x

-------------------------------------------------
-- Pattern synonyms for variables and contexts --
-------------------------------------------------

pattern zeroᵛ  = here refl
pattern sucᵛ p = there p

-- XXX This is codepoint 0x2e34.
infixl 5 _⸴_
pattern _⸴_ Γ τ = τ ∷ Γ
