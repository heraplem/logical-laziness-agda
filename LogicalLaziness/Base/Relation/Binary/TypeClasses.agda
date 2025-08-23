module LogicalLaziness.Base.Relation.Binary.TypeClasses where

open import Function
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality
  as ≡
open import Algebra
open import Data.Product
open import Data.Product.Properties
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  hiding ( ×-isPreorder
         ; ×-isPartialOrder
         )

open import LogicalLaziness.Base.Core

module _ {A : Type a} where

  private
    variable
      _∼_ _≤_ : Rel A ℓ
      _∨_     : Op₂ A
      ⊥       : A

  record IsReflexive (_∼_ : Rel A ℓ) : Type (a ⊔ℓ ℓ) where
    field
      reflexivity : ∀ {x} → x ∼ x
  open IsReflexive
    {{...}}
    public

  record IsTransitive (_∼_ : Rel A ℓ) : Type (a ⊔ℓ ℓ) where
    field
      transitivity : Transitive _∼_
  open IsTransitive
    {{...}}
    public

  record IsAntisymmetric (_≤_ : Rel A ℓ) : Type (a ⊔ℓ ℓ) where
    field
      antisymmetry : Antisymmetric _≡_ _≤_
  open IsAntisymmetric
    {{...}}
    public

  record IsJoin (_≤_ : Rel A ℓ) (_∨_ : Op₂ A) : Type (a ⊔ℓ ℓ) where
    field
      join-is-upperˡ : ∀ {x y} → x ≤ (x ∨ y)
      join-is-upperʳ : ∀ {x y} → y ≤ (x ∨ y)
      join-is-least  : ∀ {x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z
  open IsJoin
    {{...}}
    public

  isJoin⇒supremum : {{_ : IsJoin _≤_ _∨_}} → Supremum _≤_ _∨_
  isJoin⇒supremum x y
    = it .IsJoin.join-is-upperˡ
    , it .IsJoin.join-is-upperʳ
    , λ _ → it .IsJoin.join-is-least

  record IsMinimum (_≤_ : Rel A ℓ) (⊥ : A) : Type (a ⊔ℓ ℓ) where
    field
      minimality : ∀ {x} → ⊥ ≤ x
  open IsMinimum
    {{...}}
    public

  isMinimum⇒minimum : {{_ : IsMinimum _≤_ ⊥}} → Minimum _≤_ ⊥
  isMinimum⇒minimum _ = minimality

  instance

    isPreorder⇒isReflexive : {{_ : IsPreorder _≡_ _∼_}} → IsReflexive _∼_
    isPreorder⇒isReflexive .reflexivity = IsPreorder.refl it

    isPreorder⇒isTransitive : {{_ : IsPreorder _≡_ _∼_}} → IsTransitive _∼_
    isPreorder⇒isTransitive .transitivity = it .IsPreorder.trans

    isPartialOrder⇒isAntisymmetric : {{_ : IsPartialOrder _≡_ _≤_}} → IsAntisymmetric _≤_
    isPartialOrder⇒isAntisymmetric .antisymmetry = it .IsPartialOrder.antisym

    isJoinSemilattice⇒isJoin : {{_ : IsJoinSemilattice _≡_ _≤_ _∨_}} → IsJoin _≤_ _∨_
    isJoinSemilattice⇒isJoin .join-is-upperˡ = it .IsJoinSemilattice.supremum _ _ .proj₁
    isJoinSemilattice⇒isJoin .join-is-upperʳ = it .IsJoinSemilattice.supremum _ _ .proj₂ .proj₁
    isJoinSemilattice⇒isJoin .join-is-least = it .IsJoinSemilattice.supremum _ _ .proj₂ .proj₂ _

    isBoundedJoinSemilattice⇒isMinimum : {{_ : IsBoundedJoinSemilattice _≡_ _≤_ _∨_ ⊥}}
                                       → IsMinimum _≤_ ⊥
    isBoundedJoinSemilattice⇒isMinimum .minimality = it .IsBoundedJoinSemilattice.minimum _

-- open IsPartialOrder
--   {{...}}
--   public
--   using ()
--   renaming (isPreorder to isPartialOrder⇒isPreorder)

  instance
    isPartialOrder⇒isPreorder : {{_ : IsPartialOrder _≡_ _≤_}} → IsPreorder _≡_ _≤_
    isPartialOrder⇒isPreorder = IsPartialOrder.isPreorder it
  

private
  variable
    _∼₁_ _≤₁_ : Rel A ℓ₁
    _∼₂_ _≤₂_ : Rel B ℓ₂
    _∨₁_ : Op₂ A
    _∨₂_ : Op₂ B
    ⊥₁ : A
    ⊥₂ : B

instance

  ×-isReflexive : {{_ : IsReflexive _∼₁_}} {{_ : IsReflexive _∼₂_}}
                → IsReflexive (Pointwise _∼₁_ _∼₂_)
  ×-isReflexive {{it₁}} {{it₂}} .reflexivity =
    it₁ .reflexivity , it₂ .reflexivity

  ×-isTransitive : {{_ : IsTransitive _∼₁_}} {{_ : IsTransitive _∼₂_}}
                 → IsTransitive (Pointwise _∼₁_ _∼₂_)
  ×-isTransitive {{it₁}} {{it₂}} .transitivity (x₁∼x₂ , y₁∼y₂) (x₂∼x₃ , y₂∼y₃) =
    it₁ .transitivity x₁∼x₂ x₂∼x₃ , it₂ .transitivity y₁∼y₂ y₂∼y₃

  ×-isAntisymmetric : {{_ : IsAntisymmetric _≤₁_}} {{_ : IsAntisymmetric _≤₂_}}
                    → IsAntisymmetric (Pointwise _≤₁_ _≤₂_)
  ×-isAntisymmetric {{it₁}} {{it₂}} .antisymmetry (x₁∼x₂ , y₁∼y₂) (x₂∼x₁ , y₂∼y₁) =
    cong₂ _,_ (it₁ .antisymmetry x₁∼x₂ x₂∼x₁) (it₂ .antisymmetry y₁∼y₂ y₂∼y₁)

  ×-isJoin : {{_ : IsJoin _≤₁_ _∨₁_}} {{_ : IsJoin _≤₂_ _∨₂_}}
           → IsJoin (Pointwise _≤₁_ _≤₂_) (zip _∨₁_ _∨₂_)
  ×-isJoin {{it₁}} {{it₂}} .join-is-upperˡ = it₁ .join-is-upperˡ , it₂ .join-is-upperˡ
  ×-isJoin {{it₁}} {{it₂}} .join-is-upperʳ = it₁ .join-is-upperʳ , it₂ .join-is-upperʳ
  ×-isJoin {{it₁}} {{it₂}} .join-is-least (x≤₁x₃ , y₁≤y₃) (x≤₂x₃ , y₂≤y₃) =
    it₁ .join-is-least x≤₁x₃ x≤₂x₃ , it₂ .join-is-least y₁≤y₃ y₂≤y₃

  ×-isMinimum : {{_ : IsMinimum _≤₁_ ⊥₁}} {{_ : IsMinimum _≤₂_ ⊥₂}}
              → IsMinimum (Pointwise _≤₁_ _≤₂_) (⊥₁ , ⊥₂)
  ×-isMinimum {{it₁}} {{it₂}} .minimality =
    it₁ .IsMinimum.minimality , it₂ .IsMinimum.minimality

  ×-isPreorder : {{_ : IsPreorder _≡_ _≤₁_}} {{_ : IsPreorder _≡_ _≤₂_}}
               → IsPreorder _≡_ (Pointwise _≤₁_ _≤₂_)
  ×-isPreorder .IsPreorder.isEquivalence = ≡.isEquivalence
  ×-isPreorder .IsPreorder.reflexive refl = ×-isReflexive .reflexivity
  ×-isPreorder {{I1}} {{I2}} .IsPreorder.trans = ×-isTransitive {{isPreorder⇒isTransitive {{I1}}}} {{isPreorder⇒isTransitive {{I2}}}} .transitivity

  ×-isPartialOrder : {{_ : IsPartialOrder _≡_ _≤₁_}} {{_ : IsPartialOrder _≡_ _≤₂_}}
                   → IsPartialOrder _≡_ (Pointwise _≤₁_ _≤₂_)
  ×-isPartialOrder {{it₁}} {{it₂}} .IsPartialOrder.isPreorder = ×-isPreorder
  ×-isPartialOrder .IsPartialOrder.antisym = {!!}
