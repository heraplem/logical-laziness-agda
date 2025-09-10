module LogicalLaziness.Base.Effect.Monad.Tick where

open import Data.Product
open import Data.Unit
open import Data.Nat
open import Effect.Applicative
open import Effect.Functor
open import Effect.Monad

open import LogicalLaziness.Base.Core

open RawMonad {{...}}
  public

-- The Agda standard library has a writer monad, but it is implemented as a CPS
-- WriterT Identity, which is unnecessarily complicated for our purposes.  Also,
-- it accumulates on the left instead of the right.

module _ {ℓ : Level} where

  Tick : Type ℓ → Type ℓ
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
tick = tt , 1
