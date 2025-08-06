module LogicalLaziness.Base.Core where

open import Agda.Primitive
  public
  using ()
  renaming ( Set  to Type
           ; Setω to Typeω
           )

open import Relation.Nullary
  public
  using (contraposition)
open import Relation.Nullary.Decidable
  public
  using ( Dec
        ; yes
        ; no
        )
module Decidable = Relation.Nullary.Decidable
open import Relation.Binary
  public
  using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  public
  using ( _≡_
        ; refl
        ; cong
        ; isDecEquivalence
        )
open import Relation.Binary.TypeClasses
  public
open import Data.Product
  public
  using ( _×_
        ; _,_
        ; proj₁
        ; proj₂
        )
