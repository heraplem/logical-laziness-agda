module Core where

open import Agda.Primitive
  public
  using ()
  renaming ( Set  to Type
           ; Setω to Typeω
           )

open import Algebra.Bundles.Raw
open import Effect.Monad
open import Effect.Monad.Writer
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Bool
  hiding (T)
open import Data.Product
open import Data.Nat
  hiding (+-0-rawMonoid)
open import Data.List
  as List
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional

variable
  A B : Type
  P : A → Type

open RawMonad {{...}}
  public

instance
  ℕ-+-0-rawMonoid = Data.Nat.+-0-rawMonoid

  Writer-rawMonad : ∀ {w ℓ} {{𝕎 : RawMonoid w ℓ}} → RawMonad (Writer 𝕎)
  Writer-rawMonad = Effect.Monad.Writer.monad

module _ {A B : Type} (f : A → B) where

  ∈⇒∈-map : ∀ {x xs} → x ∈ xs → f x ∈ List.map f xs
  ∈⇒∈-map (here p)     = here (cong f p)
  ∈⇒∈-map (there x∈xs) = there (∈⇒∈-map x∈xs)

∈⇒lookup∈toList : ∀ {x xs} {pxs : All P xs} (x∈xs : x ∈ xs) →
  (x , All.lookup pxs x∈xs) ∈ All.toList pxs
∈⇒lookup∈toList {pxs = px ∷ pxs} (here refl)  = here refl
∈⇒lookup∈toList {pxs = px ∷ pxs} (there x∈xs) = there (∈⇒lookup∈toList x∈xs)

pattern zvar   = here refl
pattern svar p = there p

data T (A : Type) : Type where
  thunk     : A → T A
  undefined : T A

module _ (≡-dec : DecidableEquality A) where

  T-≡-dec : DecidableEquality (T A)
  T-≡-dec (thunk x) (thunk y)
   with ≡-dec x y
  ... | no x≢y   = no (λ{ refl → x≢y refl })
  ... | yes refl = yes refl
  T-≡-dec (thunk x) undefined = no (λ ())
  T-≡-dec undefined (thunk y) = no (λ ())
  T-≡-dec undefined undefined = yes refl

data ListA (A : Type) : Type where
  []  : ListA A
  _∷_ : T A → T (ListA A) → ListA A

module _ (≡-dec : DecidableEquality A) where

  ListA-≡-dec : DecidableEquality (ListA A)
  ListA-≡-dec []       []       = yes refl
  ListA-≡-dec []       (y ∷ ys) = no (λ ())
  ListA-≡-dec (x ∷ xs) []       = no (λ ())
  ListA-≡-dec (x ∷ xs) (y ∷ ys)
   with T-≡-dec ≡-dec x y
  ... | no x≢y = no (λ{ refl → x≢y refl })
  ... | yes refl
  -- Unfortunately, the termination checker won't let us use T-≡-dec here.
   with xs        | ys
  ... | undefined | undefined = yes refl
  ... | undefined | thunk ys  = no (λ ())
  ... | thunk xs  | undefined = no (λ ())
  ... | thunk xs  | thunk ys
   with ListA-≡-dec xs ys
  ... | no xs≢ys = no λ{ refl → xs≢ys refl }
  ... | yes refl = yes refl

infixl 5 _⸴_
pattern _⸴_ Γ τ = τ ∷ Γ
