module LogicalLaziness.Base.Data.List.All where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.Data.List.Membership.Propositional

∈ᴸ⇒lookup∈ᴸtoList : {x : A} {xs : List A} {pxs : All P xs} (x∈xs : x ∈ᴸ xs) →
  (x , All.lookup pxs x∈xs) ∈ᴸ All.toList pxs
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (here refl)  = here refl
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (there x∈xs) = there (∈ᴸ⇒lookup∈ᴸtoList x∈xs)

-- This complicated-looking lemma shows how to expand an application of the form
-- `η (lookup pxs x∈xs)`.
app-lookup : ∀ {q} {Q : B → Type q}
               {x : A} {xs : List A} (x∈xs : x ∈ᴸ xs)
               (pxs : All P xs)
               (f : A → B)
               (η : {x : A} → P x → Q (f x))
           → η (All.lookup pxs x∈xs) ≡ All.lookup {P = Q} (All.map⁺ (All.map η pxs)) (∈ᴸ⇒∈ᴸ-map f x∈xs)
app-lookup (here refl ) (px ∷ pxs) f η = refl
app-lookup (there x∈xs) (px ∷ pxs) f η = app-lookup x∈xs pxs f η
