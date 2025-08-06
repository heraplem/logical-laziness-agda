module LogicalLaziness.Base.ListA where

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.T
  as T
  hiding (≡-dec)

private
  variable
    A B : Type
    xT yT : T A

data ListA (A : Type) : Type where
  []  :                     ListA A
  _∷_ : T A → T (ListA A) → ListA A

foldrA : (T A → T B → B) → B → ListA A → B
foldrA f e []               = e
foldrA f e (xT ∷ thunk xsA) = f xT (thunk (foldrA f e xsA))
foldrA f e (xT ∷ undefined) = e

private
  variable
    xsT ysT : T (ListA A)

∷-injective : xT ∷ xsT ≡ yT ∷ ysT → xT ≡ yT × xsT ≡ ysT
∷-injective refl = refl , refl

module _ (_≟_ : DecidableEquality A) where

  ≡-dec : DecidableEquality (ListA A)
  ≡-dec []         []         = yes refl
  ≡-dec []         (yT ∷ ysT) = no (λ ())
  ≡-dec (xT ∷ xsT) []         = no (λ ())
  ≡-dec (xT ∷ xsT) (yT ∷ ysT)
   with T.≡-dec _≟_ xT yT
  ... | no xT≢yT = no (contraposition (λ xsA≡ysA → proj₁ (∷-injective xsA≡ysA)) xT≢yT)
  ... | yes refl
  -- Unfortunately, the termination checker won't let us use T.≡-dec here.
   with xsT        | ysT
  ... | undefined  | undefined = yes refl
  ... | undefined  | thunk ysA = no (λ ())
  ... | thunk xsA′ | undefined = no (λ ())
  ... | thunk xsA′ | thunk ysA′
   with ≡-dec xsA′ ysA′
  ... | no xsA′≢ysA′ = no (λ xsA≡ysA → xsA′≢ysA′ (thunk-injective (proj₂ (∷-injective xsA≡ysA))))
  ... | yes refl = yes refl

instance
  ListA-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = ListA A} _≡_
  ListA-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)
