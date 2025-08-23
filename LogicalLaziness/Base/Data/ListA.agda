module LogicalLaziness.Base.Data.ListA where

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.TypeClasses
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.Data.T
  as T
  hiding (≡-dec)

private
  variable
    xT yT : T A

data ListA (A : Type a) : Type a where
  []  :                     ListA A
  _∷_ : T A → T (ListA A) → ListA A

-- NOTE Inductions/recursions over `ListA` are often very annoying to define.
-- Your instinct will be to use higher-order combinators over `T`, but this will
-- usually not pass the termination checker.  You'll just have to destruct the
-- tail and define both cases manually, or else write everything in terms of
-- basic induction/recursion combinators.  I'm sorry.

private
  variable
    xsT ysT : T (ListA A)

----------------------
-- Basic operations --
----------------------

module _ (f : T A → T B → B) (e : B) where
  foldrA : ListA A → B
  foldrA []         = e
  foldrA (xT ∷ undefined) = f xT undefined
  foldrA (xT ∷ thunk xsA) = f xT (thunk (foldrA xsA))

----------------------------
-- Properties of equality --
----------------------------

∷-injective : xT ∷ xsT ≡ yT ∷ ysT → xT ≡ yT × xsT ≡ ysT
∷-injective refl = refl , refl

module _ (_≟_ : DecidableEquality A) where

  ≡-dec : DecidableEquality (ListA A)
  ≡-dec []         []         = yes refl
  ≡-dec []         (yT ∷ ysT) = no (λ ())
  ≡-dec (xT ∷ xsT) []         = no (λ ())
  ≡-dec (xT ∷ xsT) (yT ∷ ysT)
   with T.≡-dec _≟_ xT yT
  ... | no xT≢yT = no (contraposition (λ xsA≡ysA → ∷-injective xsA≡ysA .proj₁) xT≢yT)
  ... | yes refl
   with xsT        | ysT
  ... | undefined  | undefined = yes refl
  ... | undefined  | thunk ysA = no (λ ())
  ... | thunk xsA′ | undefined = no (λ ())
  ... | thunk xsA′ | thunk ysA′
   with ≡-dec xsA′ ysA′
  ... | no xsA′≢ysA′ = no (λ xsA≡ysA → xsA′≢ysA′ (thunk-injective (∷-injective xsA≡ysA .proj₂)))
  ... | yes refl     = yes refl

instance
  ListA-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = ListA A} _≡_
  ListA-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)

------------------------------
-- Lifting binary relations --
------------------------------

data Pointwise {A : Type a} {B : Type b} (_≤_ : REL A B ℓ) : REL (ListA A) (ListA B) (a ⊔ℓ b ⊔ℓ ℓ) where
  []  : Pointwise _≤_ [] []
  _∷_ : Lex _≤_ xT yT
      → Lex (Pointwise _≤_) xsT ysT
      → Pointwise _≤_ (xT ∷ xsT) (yT ∷ ysT)

-- module _ {_≤_ : Rel A ℓ} where

--   -- Properties

--   module _ (≤-reflexive : Reflexive _≤_) where
--     Pointwise-reflexive : Reflexive (Pointwise _≤_)
--     Pointwise-reflexive {x = []      } = []
--     Pointwise-reflexive {x = xT ∷ xsT} = Lex-reflexive ≤-reflexive ∷ Lex-Pointwise-reflexive
--       where
--         Lex-Pointwise-reflexive : ∀ {xsT} → Lex (Pointwise _≤_) xsT xsT
--         Lex-Pointwise-reflexive {undefined} = undefined
--         Lex-Pointwise-reflexive {thunk xsA} = thunk Pointwise-reflexive

--   module _ (≤-transitive : Transitive _≤_) where
--     open import Relation.Binary.Construct.Composition

--     Pointwise-transitive : Transitive (Pointwise _≤_)
--     Pointwise-transitive [] [] = []
--     Pointwise-transitive (xT≤yT ∷ xsT≤ysT) (yT≤zT ∷ ysT≤zsT) = Lex-transitive ≤-transitive xT≤yT yT≤zT ∷ Lex-Pointwise-transitive xsT≤ysT ysT≤zsT
--       where
--         Lex-Pointwise-transitive : ∀ {xsT ysT zsT} → Lex (Pointwise _≤_) xsT ysT → Lex (Pointwise _≤_) ysT zsT → Lex (Pointwise _≤_) xsT zsT
--         Lex-Pointwise-transitive undefined       ysT≤zsT         = undefined
--         Lex-Pointwise-transitive (thunk xsA≤ysA) (thunk ysA≤zsA) = thunk (Pointwise-transitive xsA≤ysA ysA≤zsA)

--   module _ (≤-antisymmetric : Antisymmetric _≡_ _≤_) where
--     Pointwise-antisymmetric : Antisymmetric _≡_ (Pointwise _≤_)
--     Pointwise-antisymmetric []                []                = refl
--     Pointwise-antisymmetric (xT≤yT ∷ xsT≤ysT) (yT≤xT ∷ ysT≤xsT) =
--       cong₂ _∷_ (Lex-antisymmetric ≤-antisymmetric xT≤yT yT≤xT) (Lex-Pointwise-antisymmetric xsT≤ysT ysT≤xsT)
--       where
--         Lex-Pointwise-antisymmetric : Lex (Pointwise _≤_) xsT ysT → Lex (Pointwise _≤_) ysT xsT → xsT ≡ ysT
--         Lex-Pointwise-antisymmetric undefined       undefined       = refl
--         Lex-Pointwise-antisymmetric (thunk xsA≤ysA) (thunk ysA≤xsA) = cong thunk (Pointwise-antisymmetric xsA≤ysA ysA≤xsA)

--   module _ {_∨_ : Op₂ A} (≤-reflexive : Reflexive _≤_) (≤-∨-supremum : Supremum _≤_ _∨_)where
--     Pointwise-supremum : Supremum (Pointwise _≤_) ( _∨_)
  --   Pointwise-supremum undefined yT .proj₁ = undefined
  --   Pointwise-supremum (thunk x) undefined .proj₁ = thunk ≤-reflexive
  --   Pointwise-supremum (thunk x) (thunk y) .proj₁ = thunk (≤-∨-supremum x y .proj₁)
  --   Pointwise-supremum x undefined .proj₂ .proj₁  = undefined
  --   Pointwise-supremum undefined (thunk y) .proj₂ .proj₁ = thunk ≤-reflexive
  --   Pointwise-supremum (thunk x) (thunk y) .proj₂ .proj₁ = thunk (≤-∨-supremum x y .proj₂ .proj₁)
  --   Pointwise-supremum _ _ .proj₂ .proj₂ _ undefined undefined = undefined
  --   Pointwise-supremum _ _ .proj₂ .proj₂ _ undefined (thunk x) = thunk x
  --   Pointwise-supremum _ _ .proj₂ .proj₂ _ (thunk x) undefined = thunk x
  --   Pointwise-supremum _ _ .proj₂ .proj₂ _ (thunk x) (thunk y) = thunk (≤-∨-supremum _ _ .proj₂ .proj₂ _ x y)

  -- Pointwise-minimum : Minimum (Pointwise _≤_) undefined
  -- Pointwise-minimum _ = undefined

  -- -- Bundles

  -- module _ (≤-isPreorder : IsPreorder _≡_ _≤_) where
  --   open IsPreorder
  --   Pointwise-isPreorder : IsPreorder _≡_ (Pointwise _≤_)
  --   Pointwise-isPreorder .isEquivalence = ≡.isEquivalence
  --   Pointwise-isPreorder .reflexive ≡.refl = Pointwise-reflexive (reflexive ≤-isPreorder ≡.refl)
  --   Pointwise-isPreorder .trans = Pointwise-transitive (trans ≤-isPreorder)

  -- module _ (≤-isPartialOrder : IsPartialOrder _≡_ _≤_) where
  --   open IsPartialOrder
  --   Pointwise-isPartialOrder : IsPartialOrder _≡_ (Pointwise _≤_)
  --   Pointwise-isPartialOrder .isPreorder = Pointwise-isPreorder (isPreorder ≤-isPartialOrder)
  --   Pointwise-isPartialOrder .antisym = Pointwise-antisymmetric (antisym ≤-isPartialOrder)

  -- module _ {_∨_ : Op₂ A} where

  --   module _ (≤-isJoinSemilattice : IsJoinSemilattice _≡_ _≤_ _∨_) where
  --     open IsJoinSemilattice
  --     Pointwise-isJoinSemilattice : IsJoinSemilattice _≡_ (Pointwise _≤_) (unionWith _∨_)
  --     Pointwise-isJoinSemilattice .isPartialOrder = Pointwise-isPartialOrder (isPartialOrder ≤-isJoinSemilattice)
  --     Pointwise-isJoinSemilattice .supremum =
  --       Pointwise-supremum
  --         (IsPreorder.reflexive (IsPartialOrder.isPreorder (isPartialOrder ≤-isJoinSemilattice)) ≡.refl)
  --         (supremum ≤-isJoinSemilattice)

  --     open IsBoundedJoinSemilattice
  --     Pointwise-isBoundedJoinSemilattice : IsBoundedJoinSemilattice _≡_ (Pointwise _≤_) (unionWith _∨_) undefined
  --     Pointwise-isBoundedJoinSemilattice .isJoinSemilattice = Pointwise-isJoinSemilattice
  --     Pointwise-isBoundedJoinSemilattice .minimum = Pointwise-minimum


--   instance
--     ListA-isReflexive : {{_ : IsReflexive _⊑_}} → IsReflexive (Pointwise _⊑_)
--     ListA-isReflexive .reflexivity {xsA} =
--       ind
--         (λ xsA → Pointwise _⊑_ xsA xsA)
--         []
--         (λ{ xT undefined → reflexivity ∷ undefined ; xT (thunk xsA⊑xsA) → reflexivity ∷ thunk xsA⊑xsA })
--         xsA

--   module _ {⊑-transitive : Transitive _⊑_} where
--     ListA-transitive : Transitive (Pointwise _⊑_)
--     ListA-transitive [] [] = []
--     ListA-transitive (xT⊑yT ∷ undefined) (yT⊑zT ∷ ysT⊑zsT) = T-transitive ⊑-transitive xT⊑yT {!yT⊑zT!} ∷ {!!}
--     ListA-transitive (x ∷ thunk x₁) (x₂ ∷ x₃) = {!!}

--     -- ListA-isTransitive : {{_ : IsTransitive _⊑_}} → IsTransitive (Pointwise _⊑_)
--     -- ListA-isTransitive .transitivity [] [] = []
--     -- ListA-isTransitive .transitivity (xT⊑yT ∷ undefined) (yT⊑zT ∷ ysT⊑zsT) = transitivity xT⊑yT yT⊑zT ∷ undefined
--     -- ListA-isTransitive .transitivity (xT⊑yT ∷ thunk xsA⊑ysA) (yT⊑zT ∷ thunk ysA⊑zsA) =
--     --   transitivity xT⊑yT yT⊑zT ∷ thunk (ListA-isTransitive .transitivity {!!} {!!})

--     -- ListA-isAntisymmetric : {{_ : IsAntisymmetric _⊑_}} → IsAntisymmetric (Pointwise _⊑_)
--     -- ListA-isAntisymmetric .antisymmetry x y = {!!}
