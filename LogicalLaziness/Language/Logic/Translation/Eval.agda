module LogicalLaziness.Language.Logic.Translation.Eval where

open import Data.Bool
open import Data.List
import Data.List.Relation.Unary.All.Properties
  as All

open import LogicalLaziness.Base.Data.T
open import LogicalLaziness.Base.Data.ListA
open import LogicalLaziness.Language.Explicit
  as Explicit
  using ( `Bool
        ; `T
        ; `List
        )
import LogicalLaziness.Language.Explicit.Semantics.Eval
  as 𝔼
import LogicalLaziness.Language.Logic.Translation.Base
  as Base

⟦_⟧⌊_⌋ᵗ : (α : Explicit.Ty) → 𝔼.⟦ α ⟧ᵗ → Base.⟦⌊ α ⌋⟧ᵗ
⟦ `Bool   ⟧⌊ false  ⌋ᵗ = false
⟦ `Bool   ⟧⌊ true   ⌋ᵗ = true
⟦ `T α    ⟧⌊ v      ⌋ᵗ = thunk ⟦ α ⟧⌊ v ⌋ᵗ
⟦ `List α ⟧⌊ []     ⌋ᵗ = []
⟦ `List α ⟧⌊ x ∷ xs ⌋ᵗ = ⟦ α ⟧⌊ x ⌋ᵗ ∷ thunk ⟦ `List α ⟧⌊ xs ⌋ᵗ

⌊_⌋ᵗ : {α : Explicit.Ty} → 𝔼.⟦ α ⟧ᵗ → Base.⟦⌊ α ⌋⟧ᵗ
⌊_⌋ᵗ = ⟦ _ ⟧⌊_⌋ᵗ

⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → 𝔼.⟦ Γ ⟧ᶜ → Base.⟦⌊ Γ ⌋⟧ᶜ
⟦ Γ ⟧⌊ γ ⌋ᶜ = All.gmap⁺ ⟦ _ ⟧⌊_⌋ᵗ γ

⌊_⌋ᶜ : {Γ : Explicit.Ctx} → 𝔼.⟦ Γ ⟧ᶜ → Base.⟦⌊ Γ ⌋⟧ᶜ
⌊_⌋ᶜ = ⟦ _ ⟧⌊_⌋ᶜ
