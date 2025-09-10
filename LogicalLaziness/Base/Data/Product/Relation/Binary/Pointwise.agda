module LogicalLaziness.Base.Data.Product.Relation.Binary.Pointwise where

open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality
  as ≡
  hiding ( isPreorder
         ; isPartialOrder
         )
open import Algebra
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent

open import LogicalLaziness.Base

private
  variable
    _∼₁_ _≤₁_ : Rel A ℓ
    _∼₂_ _≤₂_ : Rel B ℓ
    _·₁_ _∨₁_ : Op₂ A
    _·₂_ _∨₂_ : Op₂ B
    ⊥₁ : A
    ⊥₂ : B

-- Properties

reflexive : Reflexive _∼₁_ → Reflexive _∼₂_ → Reflexive (Pointwise _∼₁_ _∼₂_)
reflexive ∼₁-reflexive ∼₂-reflexive = ∼₁-reflexive , ∼₂-reflexive

transitive : Transitive _∼₁_ → Transitive _∼₂_ → Transitive (Pointwise _∼₁_ _∼₂_)
transitive ∼₁-transitive ∼₂-transitive (x₁∼x₂ , y₁∼y₂) (x₂∼x₃ , y₂∼y₃) =
  ∼₁-transitive x₁∼x₂ x₂∼x₃ , ∼₂-transitive y₁∼y₂ y₂∼y₃

antisymmetric : Antisymmetric _≡_ _≤₁_
              → Antisymmetric _≡_ _≤₂_
              → Antisymmetric _≡_ (Pointwise _≤₁_ _≤₂_)
antisymmetric ≤₁-antisymmetric ≤₂-antisymmetric (x₁≤x₂ , y₁≤y₂) (x₂≤x₁ , y₂≤y₁) =
  cong₂ _,_ (≤₁-antisymmetric x₁≤x₂ x₂≤x₁) (≤₂-antisymmetric y₁≤y₂ y₂≤y₁)

supremum : Supremum _≤₁_ _∨₁_ → Supremum _≤₂_ _∨₂_ → Supremum (Pointwise _≤₁_ _≤₂_) (zip _∨₁_ _∨₂_)
supremum ≤₁-supremum ≤₂-supremum (x₁ , y₁) (x₂ , y₂) =
  let (≤₁-upperˡ , ≤₁-upperʳ , ≤₁-least) = ≤₁-supremum x₁ x₂
      (≤₂-upperˡ , ≤₂-upperʳ , ≤₂-least) = ≤₂-supremum y₁ y₂
  in (≤₁-upperˡ , ≤₂-upperˡ) ,
     (≤₁-upperʳ , ≤₂-upperʳ) ,
     (λ{ _ (x₁≤x₃ , y₁≤y₂) (x₂≤x₃ , y₂≤y₂) → ≤₁-least _ x₁≤x₃ x₂≤x₃ , ≤₂-least _ y₁≤y₂ y₂≤y₂ })

minimum : Minimum _≤₁_ ⊥₁ → Minimum _≤₂_ ⊥₂ → Minimum (Pointwise _≤₁_ _≤₂_) (⊥₁ , ⊥₂)
minimum ⊥₁-minimum ⊥₂-minimum _ = ⊥₁-minimum _ , ⊥₂-minimum _

isPreorder : IsPreorder _≡_ _≤₁_
           → IsPreorder _≡_ _≤₂_
           → IsPreorder _≡_ (Pointwise _≤₁_ _≤₂_)
isPreorder ≤₁-preorder ≤₂-preorder .IsPreorder.isEquivalence = ≡.isEquivalence
isPreorder {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_} ≤₁-preorder ≤₂-preorder .IsPreorder.reflexive ≡.refl =
  reflexive
    {_∼₁_ = _≤₁_} {_∼₂_ = _≤₂_}
    (≤₁-preorder .IsPreorder.reflexive ≡.refl) (≤₂-preorder .IsPreorder.reflexive ≡.refl)
isPreorder {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_} ≤₁-preorder ≤₂-preorder .IsPreorder.trans =
  transitive
    {_∼₁_ = _≤₁_} {_∼₂_ = _≤₂_}
    (≤₁-preorder .IsPreorder.trans)
    (≤₂-preorder .IsPreorder.trans)

isPartialOrder : IsPartialOrder _≡_ _≤₁_
               → IsPartialOrder _≡_ _≤₂_
               → IsPartialOrder _≡_ (Pointwise _≤₁_ _≤₂_)
isPartialOrder ≤₁-partialOrder ≤₂-partialOrder .IsPartialOrder.isPreorder =
  isPreorder
    (≤₁-partialOrder .IsPartialOrder.isPreorder)
    (≤₂-partialOrder .IsPartialOrder.isPreorder)
isPartialOrder ≤₁-partialOrder ≤₂-partialOrder .IsPartialOrder.antisym =
  antisymmetric
    (≤₁-partialOrder .IsPartialOrder.antisym)
    (≤₂-partialOrder .IsPartialOrder.antisym)

isJoinSemilattice : IsJoinSemilattice _≡_ _≤₁_ _∨₁_
                  → IsJoinSemilattice _≡_ _≤₂_ _∨₂_
                  → IsJoinSemilattice _≡_ (Pointwise _≤₁_ _≤₂_) (zip _∨₁_ _∨₂_)
isJoinSemilattice ≤₁-joinSemilattice ≤₂-joinSemilattice .IsJoinSemilattice.isPartialOrder =
  isPartialOrder
    (≤₁-joinSemilattice .IsJoinSemilattice.isPartialOrder)
    (≤₂-joinSemilattice .IsJoinSemilattice.isPartialOrder)
isJoinSemilattice ≤₁-joinSemilattice ≤₂-joinSemilattice .IsJoinSemilattice.supremum =
  supremum
    (≤₁-joinSemilattice .IsJoinSemilattice.supremum)
    (≤₂-joinSemilattice .IsJoinSemilattice.supremum)

isBoundedJoinSemilattice
  : IsBoundedJoinSemilattice _≡_ _≤₁_ _∨₁_ ⊥₁
  → IsBoundedJoinSemilattice _≡_ _≤₂_ _∨₂_ ⊥₂
  → IsBoundedJoinSemilattice _≡_ (Pointwise _≤₁_ _≤₂_) (zip _∨₁_ _∨₂_) (⊥₁ , ⊥₂)
isBoundedJoinSemilattice ≤₁-boundedJoinSemilattice ≤₂-boundedJoinSemilattice
  .IsBoundedJoinSemilattice.isJoinSemilattice =
  isJoinSemilattice
    (≤₁-boundedJoinSemilattice .IsBoundedJoinSemilattice.isJoinSemilattice)
    (≤₂-boundedJoinSemilattice .IsBoundedJoinSemilattice.isJoinSemilattice)
isBoundedJoinSemilattice {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_}
  ≤₁-boundedJoinSemilattice ≤₂-boundedJoinSemilattice .IsBoundedJoinSemilattice.minimum =
  minimum
    {_≤₁_ = _≤₁_} {_≤₂_ = _≤₂_}
    (≤₁-boundedJoinSemilattice .IsBoundedJoinSemilattice.minimum)
    (≤₂-boundedJoinSemilattice .IsBoundedJoinSemilattice.minimum)

preserves₂ : _·₁_ Preserves₂ _∼₁_ ⟶ _∼₁_ ⟶ _∼₁_
           → _·₂_ Preserves₂ _∼₂_ ⟶ _∼₂_ ⟶ _∼₂_
           → zip _·₁_ _·₂_ Preserves₂ (Pointwise _∼₁_ _∼₂_) ⟶ (Pointwise _∼₁_ _∼₂_) ⟶ (Pointwise _∼₁_ _∼₂_)
preserves₂ φ₁ φ₂ (x₁∼x₂ , y₁∼y₂) (x₃∼x₄ , y₃∼y₄) = φ₁ x₁∼x₂ x₃∼x₄ , φ₂ y₁∼y₂ y₃∼y₄
