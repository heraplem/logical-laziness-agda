module LogicalLaziness.Language.Explicit.Semantics.Clairvoyant where

open import Data.Bool
  hiding (T)
open import Data.Product
open import Data.Nat
open import Data.List.Relation.Unary.All
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Data.T
open import LogicalLaziness.Base.Data.ListA
open import LogicalLaziness.Language.Explicit
open import LogicalLaziness.Language.Explicit.Semantics.Eval
  as 𝔼
  hiding ( ⟦_⟧ᵗ
         ; ⟦_⟧ᶜ
         ; ⟦_⟧ᵉ
         ; ⟦foldr_,_⟧ᵉ
         )

⟦_⟧ᵗ : Ty → Type
⟦ `Bool   ⟧ᵗ = Bool
⟦ `T τ    ⟧ᵗ = T ⟦ τ ⟧ᵗ
⟦ `List τ ⟧ᵗ = ListA ⟦ τ ⟧ᵗ

⟦_⟧ᶜ : Ctx → Type
⟦_⟧ᶜ = All ⟦_⟧ᵗ

private
  variable
    Γ : Ctx
    α β τ : Ty

mutual

  data ⟦_⟧ᵉ : Γ ⊢ τ → ⟦ Γ ⟧ᶜ → ⟦ τ ⟧ᵗ × ℕ → Type where
    `_ :
      ∀ {g : ⟦ Γ ⟧ᶜ}
        (x : τ ∈ᴸ Γ)
      → ⟦ ` x ⟧ᵉ g ∋ (All.lookup g x , 0)
    `let_`in_ :
      ∀ {g : ⟦ Γ ⟧ᶜ} {t₁ : Γ ⊢ α} {t₂ : Γ ⸴ α ⊢ β} {a b c₁ c₂}
      → ⟦ t₁ ⟧ᵉ g ∋ (a , c₁)
      → ⟦ t₂ ⟧ᵉ (g ⸴ a) ∋ (b , c₂)
      → ⟦ `let t₁ `in t₂ ⟧ᵉ g ∋ (b , c₁ + c₂)
    `false :
      ∀ {g : ⟦ Γ ⟧ᶜ}
      → ⟦ `false ⟧ᵉ g ∋ (false , 0)
    `true :
      ∀ {g : ⟦ Γ ⟧ᶜ}
      → ⟦ `true ⟧ᵉ g ∋ (true , 0)
    `if_`else_ :
      ∀ {g : ⟦ Γ ⟧ᶜ} {t₁} {t₂ t₃ : Γ ⊢ τ} {v c₁ c₂}
      → ⟦ t₁ ⟧ᵉ g (false , c₁)
      → ⟦ t₃ ⟧ᵉ g (v , c₂)
      → ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g (v , c₁ + c₂)
    `if_`then_ :
      ∀ {g : ⟦ Γ ⟧ᶜ} {t₁} {t₂ t₃ : Γ ⊢ τ} {v c₁ c₂}
      → ⟦ t₁ ⟧ᵉ g (true , c₁)
      → ⟦ t₂ ⟧ᵉ g (v , c₂)
      → ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g (v , c₁ + c₂)
    `[] :
      ∀ {g : ⟦ Γ ⟧ᶜ}
      → ⟦ `[] ∶ Γ ⊢ `List τ ⟧ᵉ g ∋ ([] , 0)
    _`∷_ :
      ∀ {t₁ : Γ ⊢ `T τ} {t₂ : Γ ⊢ `T (`List τ)} {g : ⟦ Γ ⟧ᶜ} {a₁ a₂ c₁ c₂}
      → ⟦ t₁ ⟧ᵉ g ∋ (a₁ , c₁)
      → ⟦ t₂ ⟧ᵉ g ∋ (a₂ , c₂)
      → ⟦ t₁ `∷ t₂ ⟧ᵉ g ∋ (a₁ ∷ a₂ , c₁ + c₂)
    `foldr :
      ∀ {t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β} {t₂ : Γ ⊢ β} {t₃ : Γ ⊢ `List α}
        {g : ⟦ Γ ⟧ᶜ} {as b c₁ c₂}
      → ⟦foldr t₁ , t₂ ⟧ᵉ g as ∋ (b , c₂)
      → ⟦ t₃ ⟧ᵉ g ∋ (as , c₁)
      → ⟦ `foldr t₁ t₂ t₃ ⟧ᵉ g ∋ (b , c₁ + c₂)
    `tick :
      ∀ {t₁ : Γ ⊢ τ} {g : ⟦ Γ ⟧ᶜ} {a c}
      → ⟦ t₁ ⟧ᵉ g ∋ (a , c)
      → ⟦ `tick t₁ ⟧ᵉ g ∋ (a , suc c)
    `lazy-undefined :
      ∀ {t₁ : Γ ⊢ τ} {g : ⟦ Γ ⟧ᶜ}
      → ⟦ `lazy t₁ ⟧ᵉ g ∋ (undefined , 0)
    `lazy-thunk :
      ∀ {t₁ : Γ ⊢ τ} {g : ⟦ Γ ⟧ᶜ} {a c}
      → ⟦ t₁ ⟧ᵉ g ∋ (a , c)
      → ⟦ `lazy t₁ ⟧ᵉ g ∋ (thunk a , c)
    `force :
      ∀ {t₁ : Γ ⊢ `T τ} {g : ⟦ Γ ⟧ᶜ} {a c}
      → ⟦ t₁ ⟧ᵉ g ∋ (thunk a , c)
      → ⟦ `force t₁ ⟧ᵉ g ∋ (a , c)

  data ⟦foldr_,_⟧ᵉ (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) (t₂ : Γ ⊢ β) : ⟦ Γ ⟧ᶜ → ListA ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ × ℕ → Type where
    `foldr-[] :
      ∀ {g b c}
      → ⟦ t₂ ⟧ᵉ g ∋ (b , c)
      → ⟦foldr t₁ , t₂ ⟧ᵉ g [] ∋ (b , c)
    `foldr-∷ :
      ∀ {g a as b b′ c₁ c₂}
      → ⟦ t₁ ⟧ᵉ (g ⸴ a ⸴ b) ∋ (b′ , c₁)
      → ⟦foldr′ t₁ , t₂ ⟧ᵉ g as ∋ (b , c₂)
      → ⟦foldr t₁ , t₂ ⟧ᵉ g (a ∷ as) ∋ (b′ , c₁ + c₂)

  data ⟦foldr′_,_⟧ᵉ (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) (t₂ : Γ ⊢ β) : ⟦ Γ ⟧ᶜ → T (ListA ⟦ α ⟧ᵗ) → T ⟦ β ⟧ᵗ × ℕ → Type where
    `foldr′-undefined :
      ∀ {g}
      → ⟦foldr′ t₁ , t₂ ⟧ᵉ g undefined ∋ (undefined , 0)
    `foldr′-thunk :
      ∀ {g as b c}
      → ⟦foldr t₁ , t₂ ⟧ᵉ g as ∋ (b , c)
      → ⟦foldr′ t₁ , t₂ ⟧ᵉ g (thunk as) ∋ (thunk b , c)
