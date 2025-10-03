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
  hiding ( rec
         ; ≡-dec
         )

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

module _ (P : ListA A → Type p) (n : P []) (c : (xT : T A) (xsT : T (ListA A)) → T.All P xsT → P (xT ∷ xsT)) where
  ind : (xs : ListA A) → P xs
  ind []               = n
  ind (xT ∷ undefined) = c xT undefined undefined
  ind (xT ∷ thunk x  ) = c xT (thunk x) (thunk (ind x))

rec : B → (T A → T B → B) → ListA A → B
rec n c = ind _ n (λ aT _ bT → c aT (T.All-const bT))

foldrA : (T A → T B → B) → B → ListA A → B
foldrA f e = rec e f

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
