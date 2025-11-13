module LogicalLaziness.Language.Logic.Translation where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool
  hiding ( T
         )
import Data.List as List
import Data.List.Relation.Unary.All.Properties
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Base.Data.T
open import LogicalLaziness.Base.Data.ListA
  as ListA
  using ( ListA
        ; []
        ; _∷_
        )
open import LogicalLaziness.Language.Explicit
  as Explicit
  using ( `Bool
        ; `T
        ; `List
        )
import LogicalLaziness.Language.Explicit.Semantics.Clairvoyant
  as ℂ
import LogicalLaziness.Language.Explicit as Explicit
open import LogicalLaziness.Language.Logic.Base
open import LogicalLaziness.Language.Logic.Renaming
open import LogicalLaziness.Language.Logic.Construct

----------------------
-- Type translation --
----------------------

⌊_⌋ᵗ : Explicit.Ty → Ty
⌊ `Bool   ⌋ᵗ = `Bool
⌊ `T A    ⌋ᵗ = `T ⌊ A ⌋ᵗ
⌊ `List A ⌋ᵗ = `ListA ⌊ A ⌋ᵗ

⌊_⌋ᶜ : Explicit.Ctx → Ctx
⌊ Γ ⌋ᶜ = List.map ⌊_⌋ᵗ Γ

--------------------------------------------------
-- Clairvoyance translation of values and terms --
--------------------------------------------------

ℂ⟦_⟧⌊_⌋ᵗ : (α : Explicit.Ty) → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
ℂ⟦_⟧⌊_⌋ᵗ′ : (α : Explicit.Ty) → ℂ.⟦ Explicit.`T α ⟧ᵗ → T ⟦ ⌊ α ⌋ᵗ ⟧ᵗ

-- Convert values.
ℂ⟦ `Bool   ⟧⌊ false   ⌋ᵗ = false
ℂ⟦ `Bool   ⟧⌊ true    ⌋ᵗ = true
ℂ⟦ `T α    ⟧⌊ v       ⌋ᵗ = ℂ⟦ α ⟧⌊ v ⌋ᵗ′
ℂ⟦ `List α ⟧⌊ []      ⌋ᵗ = []
ℂ⟦ `List α ⟧⌊ v₁ ∷ v₂ ⌋ᵗ = ℂ⟦ _ ⟧⌊ v₁ ⌋ᵗ ∷ ℂ⟦ _ ⟧⌊ v₂ ⌋ᵗ′

ℂ⟦ α ⟧⌊ undefined ⌋ᵗ′ = undefined
ℂ⟦ α ⟧⌊ thunk v   ⌋ᵗ′ = thunk ℂ⟦ α ⟧⌊ v ⌋ᵗ

ℂ⌊_⌋ᵗ : {α : Explicit.Ty} → ℂ.⟦ α ⟧ᵗ → ⟦ ⌊ α ⌋ᵗ ⟧ᵗ
ℂ⌊ v ⌋ᵗ = ℂ⟦ _ ⟧⌊ v ⌋ᵗ

ℂ⌊_⌋ᵗ-map : ∀ {α} (xs : ℂ.⟦ `List α ⟧ᵗ) → ℂ⌊ xs ⌋ᵗ ≡ ListA.map ℂ⌊_⌋ᵗ xs
ℂ⌊ []            ⌋ᵗ-map = refl
ℂ⌊ x ∷ undefined ⌋ᵗ-map = refl
ℂ⌊ x ∷ thunk xs  ⌋ᵗ-map = cong₂ _∷_ refl (cong thunk ℂ⌊ xs ⌋ᵗ-map)

ℂ⌊_⌋ᵗ-injective : ∀ {α} {v₁ v₂ : ℂ.⟦ α ⟧ᵗ}
                → ℂ⌊ v₁ ⌋ᵗ ≡ ℂ⌊ v₂ ⌋ᵗ
                → v₁ ≡ v₂
ℂ⌊_⌋ᵗ-injective {α = `Bool  } {v₁ = false    } {v₂ = false    } ψ = ψ
ℂ⌊_⌋ᵗ-injective {α = `Bool  } {v₁ = true     } {v₂ = true     } ψ = ψ
ℂ⌊_⌋ᵗ-injective {α = `T α   } {v₁ = undefined} {v₂ = undefined} ψ = refl
ℂ⌊_⌋ᵗ-injective {α = `T α   } {v₁ = thunk _  } {v₂ = thunk _  } ψ =
  cong thunk ℂ⌊ thunk-injective ψ ⌋ᵗ-injective
ℂ⌊_⌋ᵗ-injective {α = `List α} {v₁ = []       } {v₂ = []       } ψ = refl
ℂ⌊_⌋ᵗ-injective {α = `List α} {v₁ = _ ∷ _    } {v₂ = _ ∷ _    } ψ =
  let ψ₁ , ψ₂ = ListA.∷-injective ψ
  in cong₂ _∷_ ℂ⌊ ψ₁ ⌋ᵗ-injective ℂ⌊ ψ₂ ⌋ᵗ-injective

ℂ⌊_⌋ᵗ-surjective : ∀ {α} (v : ⟦ ⌊ α ⌋ᵗ ⟧ᵗ)
                → Σ[ v′ ∈ ℂ.⟦ α ⟧ᵗ ] v ≡ ℂ⌊ v′ ⌋ᵗ
ℂ⌊_⌋ᵗ-surjective {α = `Bool  } false     = false , refl
ℂ⌊_⌋ᵗ-surjective {α = `Bool  } true      = true , refl
ℂ⌊_⌋ᵗ-surjective {α = `T α   } undefined = undefined , refl
ℂ⌊_⌋ᵗ-surjective {α = `T α   } (thunk v)
 with ℂ⌊ v ⌋ᵗ-surjective
... | v′ , refl                          = thunk v′ , refl
ℂ⌊_⌋ᵗ-surjective {α = `List α} []        = [] , refl
ℂ⌊_⌋ᵗ-surjective {α = `List α} (v ∷ vs)
 with ℂ⌊ v ⌋ᵗ-surjective | ℂ⌊ vs ⌋ᵗ-surjective
... | v′ , refl          | vs′ , refl    = v′ ∷ vs′ , refl

-- Convert evaluation contexts.
ℂ⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
ℂ⟦ Γ ⟧⌊ γ ⌋ᶜ = All.gmap⁺ ℂ⟦ _ ⟧⌊_⌋ᵗ γ

ℂ⌊_⌋ᶜ : {Γ : Explicit.Ctx} → ℂ.⟦ Γ ⟧ᶜ → ⟦ ⌊ Γ ⌋ᶜ ⟧ᶜ
ℂ⌊ γ ⌋ᶜ = ℂ⟦ _ ⟧⌊ γ ⌋ᶜ

-- Convert terms.
ℂ⌊_⌋ᵉ : {Γ : Explicit.Ctx} {α : Explicit.Ty}
      → Explicit.Tm Γ α
      → ⌊ Γ ⌋ᶜ ⊢ `M ⌊ α ⌋ᵗ
ℂ⌊ Explicit.` x                      ⌋ᵉ = `return (` (∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x))
ℂ⌊ Explicit.`let t₁ `in t₂           ⌋ᵉ = ℂ⌊ t₁ ⌋ᵉ `>>= ℂ⌊ t₂ ⌋ᵉ
ℂ⌊ Explicit.`false                   ⌋ᵉ = `return `false
ℂ⌊ Explicit.`true                    ⌋ᵉ = `return `true
ℂ⌊ Explicit.`if t₁ `then t₂ `else t₃ ⌋ᵉ =
  ℂ⌊ t₁ ⌋ᵉ `>>= (`if (` zeroᵛ) `then weaken ℂ⌊ t₂ ⌋ᵉ `else weaken ℂ⌊ t₃ ⌋ᵉ)
ℂ⌊ Explicit.`[]                      ⌋ᵉ = `return `[]
ℂ⌊ t₁ Explicit.`∷ t₂                 ⌋ᵉ =
  ℂ⌊ t₁ ⌋ᵉ `>>= weaken ℂ⌊ t₂ ⌋ᵉ `>>= `return (` (sucᵛ zeroᵛ) `∷ ` zeroᵛ)
ℂ⌊ Explicit.`foldr t₁ t₂ t₃          ⌋ᵉ =
  ℂ⌊ t₃ ⌋ᵉ `>>= `foldrM (subsume₂ ℂ⌊ t₁ ⌋ᵉ) (weaken ℂ⌊ t₂ ⌋ᵉ) (` zeroᵛ)
ℂ⌊ Explicit.`tick t                  ⌋ᵉ = `tick ℂ⌊ t ⌋ᵉ
ℂ⌊ Explicit.`lazy t                  ⌋ᵉ = `lazily ℂ⌊ t ⌋ᵉ
ℂ⌊ Explicit.`force t                 ⌋ᵉ = `forced ℂ⌊ t ⌋ᵉ
