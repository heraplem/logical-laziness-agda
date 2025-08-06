module LogicalLaziness.Base where

open import Level
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Data.Unit
open import Data.Nat
  as ℕ
open import Data.List
  as List
  using ( List
        ; []
        ; _∷_
        )
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any

open import LogicalLaziness.Base.Core
  public

private
  variable
    A B : Type
    x y : A
    xs : List A
    P : A → Type
    px : P x
    pxs : All P xs

infix 4 _∋_
_∋_ : (A → Type) → A → Type
P ∋ x = P x

------------------
-- List Any/All --
------------------

-- We use _∋_ for predicates, so it would be confusing to use _∈_ for list
-- membership.  We rename it to _∈ᴸ_.
open import Data.List.Membership.Propositional
  public
  renaming (_∈_ to _∈ᴸ_)

module _ (f : A → B) where

  ∈ᴸ⇒∈ᴸ-map : x ∈ᴸ xs → f x ∈ᴸ List.map f xs
  ∈ᴸ⇒∈ᴸ-map (here p)     = here (cong f p)
  ∈ᴸ⇒∈ᴸ-map (there x∈xs) = there (∈ᴸ⇒∈ᴸ-map x∈xs)

∈ᴸ⇒lookup∈ᴸtoList : (x∈xs : x ∈ᴸ xs) →
  (x , All.lookup pxs x∈xs) ∈ᴸ All.toList pxs
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (here refl)  = here refl
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (there x∈xs) = there (∈ᴸ⇒lookup∈ᴸtoList x∈xs)

data AllPairwise (Q : ∀ {x} → P x → P x → Type) : All P xs → All P xs → Type where
  [] : AllPairwise Q [] []
  _∷_ : {px₁ px₂ : P x} {pxs₁ pxs₂ : All P xs} →
    Q px₁ px₂ →
    AllPairwise Q pxs₁ pxs₂ →
    AllPairwise Q (px₁ ∷ pxs₁) (px₂ ∷ pxs₂)

-------------------------------------------------
-- Pattern synonyms for variables and contexts --
-------------------------------------------------

pattern zeroᵛ   = here refl
pattern sucᵛ p = there p

-- XXX This is codepoint 0x2e34, NOT the ASCII comma.
infixl 5 _⸴_
pattern _⸴_ Γ τ = τ ∷ Γ

----------------
-- Tick monad --
----------------

open RawMonad {{...}}
  public

-- The Agda standard library has a writer monad, but it is implemented as a CPS
-- WriterT Identity, which is unnecessarily complicated for our purposes.  Also,
-- it accumulates on the left instead of the right.

Tick : Type → Type
Tick A = A × ℕ

instance
  rawFunctor-Tick : RawFunctor Tick
  rawFunctor-Tick = record
    { _<$>_ = λ f (x , n) → f x , n
    }

  rawApplicative-Tick : RawApplicative Tick
  rawApplicative-Tick = record
    { rawFunctor = rawFunctor-Tick
    ; pure       = (_, 0)
    ; _<*>_      = λ (f , n₁) (x , n₂) → f x , n₁ + n₂
    }

  rawMonad-Tick : RawMonad Tick
  rawMonad-Tick = record
    { rawApplicative = rawApplicative-Tick
    ; _>>=_          = λ (x , n) k → let (x′ , n′) = k x in (x′ , n + n′)
    }

tick : Tick ⊤
tick = return tt
