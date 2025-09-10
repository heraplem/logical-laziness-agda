module LogicalLaziness.Base.Data.T where

open import Relation.Nullary
import Relation.Nullary.Decidable
  as Decidable
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.Lattice
open import Relation.Binary.TypeClasses
open import Relation.Binary.PropositionalEquality
  as ≡
  using ( _≡_
        ; cong
        )
open import Algebra
open import Data.Product
  using ( proj₁
        ; proj₂
        )

open import LogicalLaziness.Base.Core

private
  variable
    x y : A

data T (A : Type a) : Type a where
  undefined :     T A
  thunk     : A → T A

private
  variable
    yT : T A

----------------------
-- Basic operations --
----------------------

rec : (A → B) → B → T A → B
rec t u undefined = u
rec t u (thunk x) = t x

map : (A → B) → T A → T B
map f undefined = undefined
map f (thunk x) = thunk (f x)

unionWith : Op₂ A → Op₂ (T A)
unionWith _·_ undefined undefined = undefined
unionWith _·_ undefined (thunk y) = thunk y
unionWith _·_ (thunk x) undefined = thunk x
unionWith _·_ (thunk x) (thunk y) = thunk (x · y)

----------------------------
-- Properties of equality --
----------------------------

thunk-injective : thunk x ≡ thunk y → x ≡ y
thunk-injective ≡.refl = ≡.refl

thunk-dec : Dec (x ≡ y) → Dec (thunk x ≡ thunk y)
thunk-dec = Decidable.map′ (cong thunk) thunk-injective

module _ (_≟_ : DecidableEquality A) where

  ≡-dec : DecidableEquality (T A)
  ≡-dec undefined undefined = yes ≡.refl
  ≡-dec undefined (thunk y) = no (λ ())
  ≡-dec (thunk x) undefined = no (λ ())
  ≡-dec (thunk x) (thunk y) = thunk-dec (x ≟ y)

instance
  T-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = T A} _≡_
  T-≡-isDecEquivalence = ≡.isDecEquivalence (≡-dec _≟_)

-----------------------------
-- Lifting unary relations --
-----------------------------

data All {a p} {A : Type a} (P : Pred A p) : Pred (T A) (a ⊔ℓ p) where
  undefined :       All P undefined
  thunk     : P x → All P (thunk x)

------------------------------
-- Lifting binary relations --
------------------------------

data Lex {a b ℓ} {A : Type a} {B : Type b} (_≤_ : REL A B ℓ) : REL (T A) (T B) (a ⊔ℓ b ⊔ℓ ℓ) where
  undefined :         Lex _≤_ undefined yT
  thunk     : x ≤ y → Lex _≤_ (thunk x) (thunk y)

module _ {_≤_ : Rel A ℓ} where

  -- Properties

  module _ (≤-reflexive : Reflexive _≤_) where
    Lex-reflexive : Reflexive (Lex _≤_)
    Lex-reflexive {x = undefined} = undefined
    Lex-reflexive {x = thunk x  } = thunk ≤-reflexive

  module _ (≤-transitive : Transitive _≤_) where
    Lex-transitive : Transitive (Lex _≤_)
    Lex-transitive undefined   yT≤zT       = undefined
    Lex-transitive (thunk x≤y) (thunk y≤z) = thunk (≤-transitive x≤y y≤z)

  module _ (≤-antisymmetric : Antisymmetric _≡_ _≤_) where
    Lex-antisymmetric : Antisymmetric _≡_ (Lex _≤_)
    Lex-antisymmetric undefined   undefined   = ≡.refl
    Lex-antisymmetric (thunk x≤y) (thunk y≤z) = cong thunk (≤-antisymmetric x≤y y≤z)

  module _ {_∨_ : Op₂ A} (≤-reflexive : Reflexive _≤_) (≤-∨-supremum : Supremum _≤_ _∨_)where
    Lex-supremum : Supremum (Lex _≤_) (unionWith _∨_)
    Lex-supremum undefined yT .proj₁ = undefined
    Lex-supremum (thunk x) undefined .proj₁ = thunk ≤-reflexive
    Lex-supremum (thunk x) (thunk y) .proj₁ = thunk (≤-∨-supremum x y .proj₁)
    Lex-supremum x undefined .proj₂ .proj₁  = undefined
    Lex-supremum undefined (thunk y) .proj₂ .proj₁ = thunk ≤-reflexive
    Lex-supremum (thunk x) (thunk y) .proj₂ .proj₁ = thunk (≤-∨-supremum x y .proj₂ .proj₁)
    Lex-supremum _ _ .proj₂ .proj₂ _ undefined undefined = undefined
    Lex-supremum _ _ .proj₂ .proj₂ _ undefined (thunk x) = thunk x
    Lex-supremum _ _ .proj₂ .proj₂ _ (thunk x) undefined = thunk x
    Lex-supremum _ _ .proj₂ .proj₂ _ (thunk x) (thunk y) = thunk (≤-∨-supremum _ _ .proj₂ .proj₂ _ x y)

  Lex-minimum : Minimum (Lex _≤_) undefined
  Lex-minimum _ = undefined

  -- Bundles

  module _ (≤-isPreorder : IsPreorder _≡_ _≤_) where
    open IsPreorder
    Lex-isPreorder : IsPreorder _≡_ (Lex _≤_)
    Lex-isPreorder .isEquivalence = ≡.isEquivalence
    Lex-isPreorder .reflexive ≡.refl = Lex-reflexive (reflexive ≤-isPreorder ≡.refl)
    Lex-isPreorder .trans = Lex-transitive (trans ≤-isPreorder)

  module _ (≤-isPartialOrder : IsPartialOrder _≡_ _≤_) where
    open IsPartialOrder
    Lex-isPartialOrder : IsPartialOrder _≡_ (Lex _≤_)
    Lex-isPartialOrder .isPreorder = Lex-isPreorder (isPreorder ≤-isPartialOrder)
    Lex-isPartialOrder .antisym = Lex-antisymmetric (antisym ≤-isPartialOrder)

  module _ {_∨_ : Op₂ A} where

    module _ (≤-isJoinSemilattice : IsJoinSemilattice _≡_ _≤_ _∨_) where
      open IsJoinSemilattice
      Lex-isJoinSemilattice : IsJoinSemilattice _≡_ (Lex _≤_) (unionWith _∨_)
      Lex-isJoinSemilattice .isPartialOrder = Lex-isPartialOrder (isPartialOrder ≤-isJoinSemilattice)
      Lex-isJoinSemilattice .supremum =
        Lex-supremum
          (IsPreorder.reflexive (IsPartialOrder.isPreorder (isPartialOrder ≤-isJoinSemilattice)) ≡.refl)
          (supremum ≤-isJoinSemilattice)

      open IsBoundedJoinSemilattice
      Lex-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≡_ (Lex _≤_) (unionWith _∨_) undefined
      Lex-isBoundedJoinSemilattice .isJoinSemilattice = Lex-isJoinSemilattice
      Lex-isBoundedJoinSemilattice .minimum = Lex-minimum
