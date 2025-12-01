module LogicalLaziness.Base.Data.List where

open import Relation.Binary.PropositionalEquality
  hiding ([_])
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.Data.List.Membership.Propositional

module _ (P : List A → Type p) (n : P []) (c : ∀ x xs → P xs → P (x ∷ xs)) where
  ind : (xs : List A) → P xs
  ind []       = n
  ind (x ∷ xs) = c x xs (ind xs)

data ++= {a} {A : Type a} (xs : List A) : List A → List A → Type a where
  [] : ++= xs xs []
  _∷_ : ∀ x xs₁ xs₂ → ++= xs (xs₁ ++ [ x ]) xs₂ → ++= xs xs₁ (x ∷ xs₂)

data List′ {a} (A : Type a) : Type a where
  [] : List′ A
  _∷′_ : List′ A → A → List′ A

data ++=′ {a} {A : Type a} (xs : List A) : List′ A → List A → Type a where
  [] : ++=′ xs [] xs
  _∷_ : ∀ x xs₁ xs₂ → ++=′ xs xs₁ (x ∷ xs₂) → ++=′ xs (xs₁ ∷′ x) xs₂

-- reverse′ : List′ A → List′ A
-- reverse′

-- reverseView′ : List′ A → List

-- open import Data.Maybe
-- open import Data.Product
-- list′ : List′ A → List A
-- list′ [] = []
-- list′ (xs ∷′ x) with list′ xs
-- ... | [] = x ∷ []
-- ... | x′ ∷ xs′ = x′ ∷ {!!}

-- ++-ind-l2r : (P : List′ A → List A → Type p)
--            → ∀ xs
--            → (∀ xs₁ xs₂ → ++=′ xs xs₁ xs₂ → P xs₁ xs₂)
--            → ∀ xs₁ xs₂ → list′ xs₁ ++ xs₂ ≡ xs → P xs₁ xs₂

module _ (P : List A → List A → Type p) {xs} (b : P xs []) (s : ∀ {x xs₁ xs₂} → P (xs₁ ++ [ x ]) xs₂ → P xs₁ (x ∷ xs₂)) where
  ++-ind-r2l : ∀ xs₁ xs₂ → xs₁ ++ xs₂ ≡ xs → P xs₁ xs₂
  ++-ind-r2l xs₁ []        refl rewrite ++-identityʳ xs₁             = b
  ++-ind-r2l xs₁ (x ∷ xs₂) ψ    rewrite sym (++-assoc xs₁ [ x ] xs₂) = s (++-ind-r2l (xs₁ ++ [ x ]) xs₂ ψ)

-- open import Data.Maybe
-- open import Data.Product
-- open import Data.List.Reverse
-- module _ (P : List A → List A → Type p) {xs} (b : P [] xs) (s : ∀ {x xs₁ xs₂} → P xs₁ (x ∷ xs₂) → P (xs₁ ++ [ x ]) xs₂) where
--   ++-ind-l2r : ∀ xs₁ xs₂ → xs₁ ++ xs₂ ≡ xs → P xs₁ xs₂
--   ++-ind-l2r xs₁ xs₂ ψ with reverseView xs₁ | inspect reverseView xs₁
--   ... | [] | _ rewrite ψ = b
--   ... | xs ∶ xs₁′ ∶ʳ x | Relation.Binary.PropositionalEquality.[ eq ] rewrite ++-assoc xs [ x ] xs₂ = s (++-ind-l2r xs (x ∷ xs₂) ψ)

-- This is a weird one, and I'm not sure what to call it.  Probably this is just
-- one facet of a more complete structure—something to do with traversing all
-- the pairs (ys, zs) such that xs = ys ++ zs.
module _ (P : List A → Type p) where
  ind-down : ∀ {xs}
           → P xs
           → (∀ {x xs′} → x ∈ᴸ xs → P (x ∷ xs′) → P xs′)
           → P []
  ind-down {xs = []    } b s = b
  ind-down {xs = x ∷ xs} b s = ind-down (s (here refl) b) (λ x∈xs → s (there x∈xs))
