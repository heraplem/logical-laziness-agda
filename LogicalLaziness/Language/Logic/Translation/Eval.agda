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
import LogicalLaziness.Language.Explicit.Semantics.Clairvoyant
  as ℂ
import LogicalLaziness.Language.Logic.Translation.Base
  as 𝕃
import LogicalLaziness.Language.Logic.Translation.Clairvoyance
  as ℂ

⟦_⟧⌊_⌋ᵗ : (α : Explicit.Ty) → 𝔼.⟦ α ⟧ᵗ → 𝕃.⟦⌊ α ⌋⟧ᵗ
⟦ α ⟧⌊ v ⌋ᵗ = ℂ.⟦ α ⟧⌊ ℂ.𝔼⟦ α ⟧[ v ]ᵗ ⌋ᵗ
-- ⟦ `Bool   ⟧⌊ false  ⌋ᵗ = false
-- ⟦ `Bool   ⟧⌊ true   ⌋ᵗ = true
-- ⟦ `T α    ⟧⌊ v      ⌋ᵗ = thunk ⟦ α ⟧⌊ v ⌋ᵗ
-- ⟦ `List α ⟧⌊ []     ⌋ᵗ = []
-- ⟦ `List α ⟧⌊ x ∷ xs ⌋ᵗ = ⟦ α ⟧⌊ x ⌋ᵗ ∷ thunk ⟦ `List α ⟧⌊ xs ⌋ᵗ

⌊_⌋ᵗ : ∀ {α} → 𝔼.⟦ α ⟧ᵗ → 𝕃.⟦⌊ α ⌋⟧ᵗ
⌊_⌋ᵗ = ⟦ _ ⟧⌊_⌋ᵗ

⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → 𝔼.⟦ Γ ⟧ᶜ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⟦ Γ ⟧⌊ γ ⌋ᶜ = ℂ.⟦ Γ ⟧⌊ ℂ.𝔼⟦ Γ ⟧[ γ ]ᶜ ⌋ᶜ

⌊_⌋ᶜ : ∀ {Γ} → 𝔼.⟦ Γ ⟧ᶜ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⌊_⌋ᶜ = ⟦ _ ⟧⌊_⌋ᶜ
