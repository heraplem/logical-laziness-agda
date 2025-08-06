module LogicalLaziness.Base.T where

open import LogicalLaziness.Base.Core

private
  variable
    A B : Type
    x y : A

data T (A : Type) : Type where
  thunk     : A → T A
  undefined :     T A

rec : (A → B) → B → T A → B
rec f y (thunk x) = f x
rec f y undefined = y

thunk-injective : thunk x ≡ thunk y → x ≡ y
thunk-injective refl = refl

thunk-dec : Dec (x ≡ y) → Dec (thunk x ≡ thunk y)
thunk-dec = Decidable.map′ (cong thunk) thunk-injective

module _ (_≟_ : DecidableEquality A) where

  ≡-dec : DecidableEquality (T A)
  ≡-dec (thunk x) (thunk y) = thunk-dec (x ≟ y)
  ≡-dec (thunk x) undefined = no (λ ())
  ≡-dec undefined (thunk y) = no (λ ())
  ≡-dec undefined undefined = yes refl

instance
  T-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = T A} _≡_
  T-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)

map : (A → B) → T A → T B
map f (thunk x) = thunk (f x)
map f undefined = undefined
