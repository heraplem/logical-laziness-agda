module LogicalLaziness.Language.Clairvoyant where

open import Function.Properties
open import Level
  using (0ℓ; Lift)
open import Relation.Binary
open import Relation.Binary.Lattice
open import Data.Nat
  hiding (_≤_)
open import Data.Maybe
open import Data.Product
open import LogicalLaziness.Base

variable
  c c₁ c₂ ℓ₁ ℓ₁₁ ℓ₁₂ ℓ₂ ℓ₂₁ ℓ₂₂ : Level

-- ℕ-Lattice : Lattice 0ℓ 0ℓ
-- ℕ-Lattice = record
--   { Carrier   = ℕ
--   ; _≈_       = _≡_
--   ; _∨_       = _⊔_
--   ; _∧_       = _⊓_
--   ; isLattice = record
--     { isEquivalence = {!!}
--     ; ∨-comm        = {!!}
--     ; ∨-assoc       = {!!}
--     ; ∨-cong        = {!!}
--     ; ∧-comm        = {!!}
--     ; ∧-assoc       = {!!}
--     ; ∧-cong        = {!!}
--     ; absorptive    = {!!}
--     }
--   }

module _ {LB : Lattice c ℓ₁ ℓ₂} where

  open Lattice LB
    renaming ( Carrier to L
             ; isPartialOrder to ≤-isPartialOrder
             )

  open import Relation.Binary.Construct.Add.Point.Equality _≈_
    public
    using ()
    renaming (_≈∙_ to _≈⊥_)

  open import Relation.Binary.Construct.Add.Infimum.NonStrict _≤_
    as ≤₋
    public
    using ( ⊥₋≤_
          ; [_]
          )
    renaming (_≤₋_ to _≤⊥_)

  ≤⊥-isPartialOrder : IsPartialOrder _≈⊥_ _≤⊥_
  ≤⊥-isPartialOrder = ≤₋.≤₋-isPartialOrder ≤-isPartialOrder

  _∨⊥_ : Maybe L → Maybe L → Maybe L
  just x ∨⊥ just y = just (x ∨ y)
  just x ∨⊥ nothing = just x
  nothing ∨⊥ just y = just y
  nothing ∨⊥ nothing = nothing

  _∧⊥_ : Maybe L → Maybe L → Maybe L
  just x₁ ∧⊥ just x₂ = just (x₁ ∧ x₂)
  just x₁ ∧⊥ nothing = nothing
  nothing ∧⊥ just x₂ = nothing
  nothing ∧⊥ nothing = nothing

  ≤⊥-∨⊥-supremum : Supremum _≤⊥_ _∨⊥_
  ≤⊥-∨⊥-supremum (just x) (just x₁) .proj₁ = [ supremum x x₁ .proj₁ ]
  ≤⊥-∨⊥-supremum (just x) nothing .proj₁ = [ reflexive Eq.refl ]
  ≤⊥-∨⊥-supremum nothing (just x) .proj₁ = ⊥₋≤ (nothing ∨⊥ just x)
  ≤⊥-∨⊥-supremum nothing nothing .proj₁ = ⊥₋≤ (nothing ∨⊥ nothing)
  ≤⊥-∨⊥-supremum (just x) (just x₁) .proj₂ .proj₁ = [ supremum x x₁ .proj₂ .proj₁ ]
  ≤⊥-∨⊥-supremum (just x) nothing .proj₂ .proj₁ = ⊥₋≤ (just x ∨⊥ nothing)
  ≤⊥-∨⊥-supremum nothing (just x) .proj₂ .proj₁ = [ reflexive Eq.refl ]
  ≤⊥-∨⊥-supremum nothing nothing .proj₂ .proj₁ = ⊥₋≤ (nothing ∨⊥ nothing)
  ≤⊥-∨⊥-supremum _ _ .proj₂ .proj₂ _ (⊥₋≤ _) (⊥₋≤ _) = ⊥₋≤ _
  ≤⊥-∨⊥-supremum _ _ .proj₂ .proj₂ _ (⊥₋≤ .(just _)) [ x ] = [ x ]
  ≤⊥-∨⊥-supremum _ _ .proj₂ .proj₂ _ [ x ] (⊥₋≤ .(just _)) = [ x ]
  ≤⊥-∨⊥-supremum _ _ .proj₂ .proj₂ _ [ x ] [ x₁ ] = [ supremum _ _ .proj₂ .proj₂ _ x x₁ ]

  ≤⊥-∧⊥-infimum : Infimum _≤⊥_ _∧⊥_
  ≤⊥-∧⊥-infimum (just x) (just x₁) .proj₁ = [ infimum x x₁ .proj₁ ]
  ≤⊥-∧⊥-infimum (just x) nothing .proj₁ = ⊥₋≤ just x
  ≤⊥-∧⊥-infimum nothing (just x) .proj₁ = ⊥₋≤ nothing
  ≤⊥-∧⊥-infimum nothing nothing .proj₁ = ⊥₋≤ nothing
  ≤⊥-∧⊥-infimum (just x) (just x₁) .proj₂ .proj₁ = [ infimum x x₁ .proj₂ .proj₁ ]
  ≤⊥-∧⊥-infimum (just x) nothing .proj₂ .proj₁ = ⊥₋≤ nothing
  ≤⊥-∧⊥-infimum nothing (just x) .proj₂ .proj₁ = ⊥₋≤ just x
  ≤⊥-∧⊥-infimum nothing nothing .proj₂ .proj₁ = ⊥₋≤ nothing
  ≤⊥-∧⊥-infimum x y .proj₂ .proj₂ z (⊥₋≤ .x) (⊥₋≤ .y) = ⊥₋≤ (x ∧⊥ y)
  ≤⊥-∧⊥-infimum x y .proj₂ .proj₂ z [ x₁ ] [ x₂ ] = [ infimum _ _ .proj₂ .proj₂ _ x₁ x₂ ]

  _⊥ : Lattice c (c Level.⊔ ℓ₁) (c Level.⊔ ℓ₂)
  _⊥ = record
        { Carrier = Maybe L
        ; _≈_ = _≈⊥_
        ; _≤_ = _≤⊥_
        ; _∨_ = _∨⊥_
        ; _∧_ = _∧⊥_
        ; isLattice = record
          { isPartialOrder = ≤⊥-isPartialOrder
          ; supremum = ≤⊥-∨⊥-supremum
          ; infimum = ≤⊥-∧⊥-infimum
          }
        }
