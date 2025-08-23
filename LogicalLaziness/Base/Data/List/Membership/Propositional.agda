module LogicalLaziness.Base.Data.List.Membership.Propositional where

open import Relation.Binary.PropositionalEquality
open import Data.List
  as List
open import Data.List.Relation.Unary.Any

open import LogicalLaziness.Base.Core

-- We use _∋_ for predicates, so it would be confusing to use _∈_ for list
-- membership.  We rename it to _∈ᴸ_.
open import Data.List.Membership.Propositional
  public
  renaming (_∈_ to _∈ᴸ_)

module _ (f : A → B) where

  ∈ᴸ⇒∈ᴸ-map : {x : A} {xs : List A} → x ∈ᴸ xs → f x ∈ᴸ List.map f xs
  ∈ᴸ⇒∈ᴸ-map (here p)     = here (cong f p)
  ∈ᴸ⇒∈ᴸ-map (there x∈xs) = there (∈ᴸ⇒∈ᴸ-map x∈xs)
