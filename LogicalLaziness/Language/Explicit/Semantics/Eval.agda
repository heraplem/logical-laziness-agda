module LogicalLaziness.Language.Explicit.Semantics.Eval where

open import Data.Bool
open import Data.List
open import Data.List.Relation.Unary.All
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Language.Explicit

private
  variable
    Γ : Ctx
    α α₁ α₂ : Ty

⟦_⟧ᵗ : Ty → Type
⟦ `Bool    ⟧ᵗ = Bool
⟦ `T α₁    ⟧ᵗ = ⟦ α₁ ⟧ᵗ
⟦ `List α₁ ⟧ᵗ = List ⟦ α₁ ⟧ᵗ

⟦_⟧ᶜ : Ctx → Type
⟦_⟧ᶜ = All ⟦_⟧ᵗ

private
  variable
    γ : ⟦ Γ ⟧ᶜ

⟦_⟧ᵉ
  : Γ ⊢ α
  → ⟦ Γ ⟧ᶜ → ⟦ α ⟧ᵗ

⟦if_,_⟧ᵉ
  : Γ ⊢ α → Γ ⊢ α
  → ⟦ Γ ⟧ᶜ → Bool → ⟦ α ⟧ᵗ

⟦foldr_,_⟧ᵉ
  : Γ ⸴ `T α₁ ⸴ `T α₂ ⊢ α₂ → Γ ⊢ α₂
  → ⟦ Γ ⟧ᶜ → List ⟦ α₁ ⟧ᵗ → ⟦ α₂ ⟧ᵗ

⟦ ` x                      ⟧ᵉ γ = All.lookup γ x
⟦ `let t₁ `in t₂           ⟧ᵉ γ = let v = ⟦ t₁ ⟧ᵉ γ in ⟦ t₂ ⟧ᵉ (γ ⸴ v)
⟦ `false                   ⟧ᵉ γ = false
⟦ `true                    ⟧ᵉ γ = true
⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ = ⟦if t₂ , t₃ ⟧ᵉ γ (⟦ t₁ ⟧ᵉ γ)
⟦ `[]                      ⟧ᵉ γ = []
⟦ t₁ `∷ t₂                 ⟧ᵉ γ = ⟦ t₁ ⟧ᵉ γ ∷ ⟦ t₂ ⟧ᵉ γ
⟦ `foldr t₁ t₂ t₃          ⟧ᵉ γ = ⟦foldr t₁ , t₂ ⟧ᵉ γ (⟦ t₃ ⟧ᵉ γ)
⟦ `tick t₁                 ⟧ᵉ γ = ⟦ t₁ ⟧ᵉ γ
⟦ `lazy t₁                 ⟧ᵉ γ = ⟦ t₁ ⟧ᵉ γ
⟦ `force t₁                ⟧ᵉ γ = ⟦ t₁ ⟧ᵉ γ

⟦if t₁ , t₂ ⟧ᵉ γ v = if v then ⟦ t₁ ⟧ᵉ γ else ⟦ t₂ ⟧ᵉ γ

⟦foldr t₁ , t₂ ⟧ᵉ γ = foldr (λ v₁ v₂ → ⟦ t₁ ⟧ᵉ (γ ⸴ v₁ ⸴ v₂)) (⟦ t₂ ⟧ᵉ γ)
