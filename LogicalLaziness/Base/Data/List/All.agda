module LogicalLaziness.Base.Data.List.All where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.Data.List.Membership.Propositional

∈ᴸ⇒lookup∈ᴸtoList : {x : A} {xs : List A} {pxs : All P xs} (x∈xs : x ∈ᴸ xs) →
  (x , All.lookup pxs x∈xs) ∈ᴸ All.toList pxs
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (here refl)  = here refl
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (there x∈xs) = there (∈ᴸ⇒lookup∈ᴸtoList x∈xs)
