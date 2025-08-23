module LogicalLaziness.Base.Data.List.All.Relation.Binary.Pointwise where

open import Relation.Unary
  hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality
  as ≡
  using ( _≡_
        ; cong₂
        )
open import Data.Product
open import Data.List
  using ( List
        ; []
        ; _∷_
        )
open import Data.List.Relation.Unary.All
  as All
  using ( All
        ; []
        ; _∷_
        )
open import Data.List.Relation.Unary.Any
  using ( here
        ; there
        )
open import Data.List.Membership.Propositional
open import LogicalLaziness.Base.Core

private
  variable
    x : A
    xs : List A
    pxs₁ pxs₂ : All P xs

data Pointwise {a p} {A : Type a} {P : Pred A p} (_∼_ : ∀ {x} → P x → P x → Type ℓ) : All P xs → All P xs → Type (a ⊔ℓ p ⊔ℓ ℓ) where
  []  : Pointwise _∼_ [] []
  _∷_ : {px₁ px₂ : P x} {pxs₁ pxs₂ : All P xs}
      → px₁ ∼ px₂
      → Pointwise _∼_ pxs₁ pxs₂
      → Pointwise _∼_ (px₁ ∷ pxs₁) (px₂ ∷ pxs₂)

-- lookup : ∀ {P} {pxs₁ pxs₂ : All P xs}
--            {R : ∀ {x} → P x → P x → Type}
--        → Pointwise R pxs₁ pxs₂
--        → (x∈xs : x ∈ xs)
--        → R {x} (All.lookup {P = P} pxs₁ x∈xs) (All.lookup {P = P} pxs₂ x∈xs)
-- lookup (rpx₁px₂ ∷ _)   (here ≡.refl) = rpx₁px₂
-- lookup (_ ∷ rpxs₁pxs₂) (there x∈xs)  = lookup rpxs₁pxs₂ x∈xs

updateAt : (x∈xs : x ∈ xs)
           {R : ∀ {x} → P x → P x → Type}
           {pxs₁ pxs₂ : All P xs}
           {f₁ f₂ : P x → P x}
         → ({px₁ px₂ : P x} → R px₁ px₂ → R (f₁ px₁) (f₂ px₂))
         → Pointwise R pxs₁ pxs₂
         → Pointwise R (All.updateAt x∈xs f₁ pxs₁) (All.updateAt x∈xs f₂ pxs₂)
updateAt (here ≡.refl) rfr (rpx₁px₂ ∷ rpxs₁pxs₂) = rfr rpx₁px₂ ∷ rpxs₁pxs₂
updateAt (there x∈xs)  rfr (rpx₁px₂ ∷ rpxs₁pxs₂) = rpx₁px₂ ∷ updateAt x∈xs rfr rpxs₁pxs₂

private
  variable
    _∼_ : ∀ {x} → P x → P x → Type ℓ
    _≤_ : ∀ {x} → P x → P x → Type ℓ
    _∨_ : ∀ {x} → P x → P x → P x
    ⊥ : ∀ {x} → P x

-- Properties

module _ (∼-reflexive : (∀ {x} → Reflexive (_∼_ {x}))) where
  reflexive : Reflexive (Pointwise (λ {x} → _∼_ {x}) {xs = xs})
  reflexive {xs = []    } {x = []      } = []
  reflexive {xs = x ∷ xs} {x = px ∷ pxs} = ∼-reflexive ∷ reflexive

module _ (∼-transitive : (∀ {x} → Transitive (_∼_ {x}))) where
  transitive : Transitive (Pointwise (λ {x} → _∼_ {x}) {xs = xs})
  transitive []                []                = []
  transitive (qpxpy ∷ qpxspys) (qpypz ∷ qpyspzs) =
    ∼-transitive qpxpy qpypz ∷ transitive qpxspys qpyspzs

module _ (≤-antisymmetric : (∀ {x} → Antisymmetric _≡_ (_≤_ {x}))) where
  antisymmetric : Antisymmetric _≡_ (Pointwise (λ {x} → _≤_ {x}) {xs = xs})
  antisymmetric []                []                = ≡.refl
  antisymmetric (qpxpy ∷ qpxspys) (qpypx ∷ qpyspxs) =
    cong₂ _∷_ (≤-antisymmetric qpxpy qpypx) (antisymmetric qpxspys qpyspxs)

module _ (≤-supremum : ∀ {x} → Supremum (_≤_ {x}) (_∨_ {x})) where
  supremum :
    Supremum
      (Pointwise (λ {x} → _≤_ {x}) {xs = xs})
      (curry (All.zipWith (uncurry _∨_)))
  supremum []         []         .proj₁ = []
  supremum (px ∷ pxs) (py ∷ pys) .proj₁ = ≤-supremum px py .proj₁ ∷ supremum pxs pys .proj₁
  supremum []         []         .proj₂ .proj₁ = []
  supremum (px ∷ pxs) (py ∷ pys) .proj₂ .proj₁ =
    ≤-supremum px py .proj₂ .proj₁ ∷ supremum pxs pys .proj₂ .proj₁
  supremum _ _ .proj₂ .proj₂ _ []                 []                 = []
  supremum _ _ .proj₂ .proj₂ _ (px≤pys ∷ pxs≤pys) (py≤pzs ∷ pys≤pzs) =
    ≤-supremum _ _ .proj₂ .proj₂ _ px≤pys py≤pzs ∷ supremum _ _ .proj₂ .proj₂ _ pxs≤pys pys≤pzs

module _ (≤-minimum : ∀ {x} → Minimum (_≤_ {x}) (⊥ {x})) where
  minimum : Minimum (Pointwise (λ {x} → _≤_ {x})) (All.universal (λ _ → ⊥) xs)
  minimum []         = []
  minimum (px ∷ pxs) = ≤-minimum px ∷ minimum pxs

-- Bundles

module _ (≤-isPreorder : (∀ {x} → IsPreorder _≡_ (_≤_ {x}))) where
  isPreorder : ∀ {x} → IsPreorder _≡_ (Pointwise (_≤_ {x}) {xs = xs})
  isPreorder .IsPreorder.isEquivalence =
    ≡.isEquivalence
  isPreorder .IsPreorder.reflexive ≡.refl =
    reflexive (≤-isPreorder .IsPreorder.reflexive ≡.refl)
  isPreorder .IsPreorder.trans =
    transitive (≤-isPreorder .IsPreorder.trans)

module _ (≤-isPartialOrder : (∀ {x} → IsPartialOrder _≡_ (_≤_ {x}))) where
  isPartialOrder : IsPartialOrder _≡_ (Pointwise (_≤_ {x}) {xs = xs})
  isPartialOrder .IsPartialOrder.isPreorder =
    isPreorder (λ {x} → ≤-isPartialOrder {x} .IsPartialOrder.isPreorder)
  isPartialOrder .IsPartialOrder.antisym =
    antisymmetric (≤-isPartialOrder .IsPartialOrder.antisym)

module _ (≤-isJoinSemilattice : (∀ {x} → IsJoinSemilattice _≡_ (_≤_ {x}) (_∨_ {x}))) where
  isJoinSemilattice : IsJoinSemilattice _≡_ (Pointwise (_≤_ {x}) {xs = xs}) (curry (All.zipWith (uncurry _∨_)))
  isJoinSemilattice .IsJoinSemilattice.isPartialOrder =
    isPartialOrder (λ {x} → ≤-isJoinSemilattice {x} .IsJoinSemilattice.isPartialOrder)
  isJoinSemilattice .IsJoinSemilattice.supremum =
    supremum (≤-isJoinSemilattice .IsJoinSemilattice.supremum)

module _ {⊥ : ∀ {x} → P x} (≤-isBoundedJoinSemilattice : (∀ {x} → IsBoundedJoinSemilattice _≡_ (_≤_ {x}) (_∨_ {x}) (⊥ {x}))) where
  isBoundedJoinSemilattice :
    IsBoundedJoinSemilattice
      _≡_
      (Pointwise (_≤_ {x}) {xs = xs})
      (curry (All.zipWith (uncurry _∨_)))
      (All.universal (λ _ → ⊥) _)
  isBoundedJoinSemilattice .IsBoundedJoinSemilattice.isJoinSemilattice =
    isJoinSemilattice (λ {x} → ≤-isBoundedJoinSemilattice {x} .IsBoundedJoinSemilattice.isJoinSemilattice)
  isBoundedJoinSemilattice .IsBoundedJoinSemilattice.minimum =
    minimum (≤-isBoundedJoinSemilattice .IsBoundedJoinSemilattice.minimum)
