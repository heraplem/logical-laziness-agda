module LogicalLaziness.Base.Data.ListA where

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.TypeClasses
open import Relation.Binary.PropositionalEquality
open import Data.Product
  hiding ( map
         )
open import Data.List
  hiding ( map
         )

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.Data.T
  as T
  hiding ( rec
         ; map
         ; ≡-dec
         )

private
  variable
    x y : A

data ListA (A : Type a) : Type a where
  []  :                   ListA A
  _∷_ : A → T (ListA A) → ListA A

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

module _ (P : ListA A → Type p) (n : P []) (c : (x : A) (xsT : T (ListA A)) → T.All P xsT → P (x ∷ xsT)) where
  ind : (xs : ListA A) → P xs
  ind []               = n
  ind (xT ∷ undefined) = c xT undefined undefined
  ind (xT ∷ thunk x  ) = c xT (thunk x) (thunk (ind x))

rec : B → (A → T B → B) → ListA A → B
rec n c = ind _ n (λ a _ bT → c a (T.All-const bT))

foldrA : (A → T B → B) → B → ListA A → B
foldrA f e = rec e f

module _ (f : A → B) where
  map : ListA A → ListA B
  map []              = []
  map (x ∷ undefined) = f x ∷ undefined
  map (x ∷ thunk xs)  = f x ∷ thunk (map xs)

----------------------------
-- Properties of equality --
----------------------------

∷-injective : x ∷ xsT ≡ y ∷ ysT → x ≡ y × xsT ≡ ysT
∷-injective refl = refl , refl

module _ (_≟_ : DecidableEquality A) where

  ≡-dec : DecidableEquality (ListA A)
  ≡-dec []        []        = yes refl
  ≡-dec []        (y ∷ ysT) = no (λ ())
  ≡-dec (x ∷ xsT) []        = no (λ ())
  ≡-dec (x ∷ xsT) (y ∷ ysT)
   with x ≟ y
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
  _∷_ : x ≤ y
      → Lex (Pointwise _≤_) xsT ysT
      → Pointwise _≤_ (x ∷ xsT) (y ∷ ysT)
