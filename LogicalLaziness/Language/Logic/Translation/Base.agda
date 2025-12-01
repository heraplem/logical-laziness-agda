module LogicalLaziness.Language.Logic.Translation.Base where

import Data.List as List
open import LogicalLaziness.Base
open import LogicalLaziness.Language.Explicit
  as Explicit
  using ( `Bool
        ; `T
        ; `List
        )
open import LogicalLaziness.Language.Logic.Base
open import LogicalLaziness.Language.Logic.Construct

----------------------
-- Type translation --
----------------------

⌊_⌋ᵗ : Explicit.Ty → Ty
⌊ `Bool   ⌋ᵗ = `Bool
⌊ `T A    ⌋ᵗ = `T ⌊ A ⌋ᵗ
⌊ `List A ⌋ᵗ = `ListA ⌊ A ⌋ᵗ

⟦⌊_⌋⟧ᵗ : Explicit.Ty → Type
⟦⌊ α ⌋⟧ᵗ = ⟦ ⌊ α ⌋ᵗ ⟧ᵗ

⌊_⌋ᶜ : Explicit.Ctx → Ctx
⌊ Γ ⌋ᶜ = List.map ⌊_⌋ᵗ Γ

⟦⌊_⌋⟧ᶜ : Explicit.Ctx → Type
⟦⌊ α ⌋⟧ᶜ = ⟦ ⌊ α ⌋ᶜ ⟧ᶜ
