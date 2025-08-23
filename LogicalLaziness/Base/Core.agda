module LogicalLaziness.Base.Core where

open import Agda.Primitive
  public
  using ()
  renaming ( Set  to Type
           ; Setω to Typeω
           )
open import Level
  public
  using ( Level
        ; 0ℓ
        )
  renaming ( suc to sucℓ
           ; _⊔_ to _⊔ℓ_
           )

variable
  a b c p ℓ ℓ₁ ℓ₂ : Level
  A : Type a
  B : Type b
  C : Type c
  P : A → Type p
