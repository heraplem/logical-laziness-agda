module LogicalLaziness.Language.Logic.Translation.Clairvoyance where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool
  hiding ( T
         )
import Data.List.Relation.Unary.All.Properties
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Effect.Monad.Tick
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
import LogicalLaziness.Language.Logic.Translation.Base
 as 𝕃

--------------------------------------------------
-- Clairvoyance translation of values and terms --
--------------------------------------------------

-- Convert values

⟦_⟧⌊_⌋ᵗ : (α : Explicit.Ty) → ℂ.⟦ α ⟧ᵗ → 𝕃.⟦⌊ α ⌋⟧ᵗ
⟦_⟧⌊_⌋ᵗ′ : (α : Explicit.Ty) → ℂ.⟦ Explicit.`T α ⟧ᵗ → T 𝕃.⟦⌊ α ⌋⟧ᵗ

⟦ `Bool   ⟧⌊ false   ⌋ᵗ = false
⟦ `Bool   ⟧⌊ true    ⌋ᵗ = true
⟦ `T α    ⟧⌊ v       ⌋ᵗ = ⟦ α ⟧⌊ v ⌋ᵗ′
⟦ `List α ⟧⌊ []      ⌋ᵗ = []
⟦ `List α ⟧⌊ v₁ ∷ v₂ ⌋ᵗ = ⟦ _ ⟧⌊ v₁ ⌋ᵗ ∷ ⟦ _ ⟧⌊ v₂ ⌋ᵗ′

⟦ α ⟧⌊ undefined ⌋ᵗ′ = undefined
⟦ α ⟧⌊ thunk v   ⌋ᵗ′ = thunk ⟦ α ⟧⌊ v ⌋ᵗ

⌊_⌋ᵗ : {α : Explicit.Ty} → ℂ.⟦ α ⟧ᵗ → 𝕃.⟦⌊ α ⌋⟧ᵗ
⌊ v ⌋ᵗ = ⟦ _ ⟧⌊ v ⌋ᵗ

-- Properties of value conversion

⌊_⌋ᵗ-injective : ∀ {α} {v₁ v₂ : ℂ.⟦ α ⟧ᵗ}
               → ⌊ v₁ ⌋ᵗ ≡ ⌊ v₂ ⌋ᵗ
               → v₁ ≡ v₂
⌊_⌋ᵗ-injective {α = `Bool  } {v₁ = false    } {v₂ = false    } ψ = ψ
⌊_⌋ᵗ-injective {α = `Bool  } {v₁ = true     } {v₂ = true     } ψ = ψ
⌊_⌋ᵗ-injective {α = `T α   } {v₁ = undefined} {v₂ = undefined} ψ = refl
⌊_⌋ᵗ-injective {α = `T α   } {v₁ = thunk _  } {v₂ = thunk _  } ψ =
  cong thunk ⌊ thunk-injective ψ ⌋ᵗ-injective
⌊_⌋ᵗ-injective {α = `List α} {v₁ = []       } {v₂ = []       } ψ = refl
⌊_⌋ᵗ-injective {α = `List α} {v₁ = _ ∷ _    } {v₂ = _ ∷ _    } ψ =
  let ψ₁ , ψ₂ = ListA.∷-injective ψ
  in cong₂ _∷_ ⌊ ψ₁ ⌋ᵗ-injective ⌊ ψ₂ ⌋ᵗ-injective

⌊_⌋ᵗ-surjective : ∀ {α} (v : 𝕃.⟦⌊ α ⌋⟧ᵗ)
               → Σ[ v′ ∈ ℂ.⟦ α ⟧ᵗ ] v ≡ ⌊ v′ ⌋ᵗ
⌊_⌋ᵗ-surjective {α = `Bool  } false     = false , refl
⌊_⌋ᵗ-surjective {α = `Bool  } true      = true , refl
⌊_⌋ᵗ-surjective {α = `T α   } undefined = undefined , refl
⌊_⌋ᵗ-surjective {α = `T α   } (thunk v)
 with ⌊ v ⌋ᵗ-surjective
... | v′ , refl                          = thunk v′ , refl
⌊_⌋ᵗ-surjective {α = `List α} []        = [] , refl
⌊_⌋ᵗ-surjective {α = `List α} (v ∷ vs)
 with ⌊ v ⌋ᵗ-surjective | ⌊ vs ⌋ᵗ-surjective
... | v′ , refl         | vs′ , refl    = v′ ∷ vs′ , refl

⌊_⌋ᵗ-map : ∀ {α} (xs : ℂ.⟦ `List α ⟧ᵗ) → ⌊ xs ⌋ᵗ ≡ ListA.map ⌊_⌋ᵗ xs
⌊ []            ⌋ᵗ-map = refl
⌊ x ∷ undefined ⌋ᵗ-map = refl
⌊ x ∷ thunk xs  ⌋ᵗ-map = cong₂ _∷_ refl (cong thunk ⌊ xs ⌋ᵗ-map)

-- Convert evaluation contexts

⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → ℂ.⟦ Γ ⟧ᶜ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⟦ Γ ⟧⌊ γ ⌋ᶜ = All.gmap⁺ ⟦ _ ⟧⌊_⌋ᵗ γ

⌊_⌋ᶜ : {Γ : Explicit.Ctx} → ℂ.⟦ Γ ⟧ᶜ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⌊ γ ⌋ᶜ = ⟦ _ ⟧⌊ γ ⌋ᶜ

-- Convert terms

⌊_⌋ᵉ : {Γ : Explicit.Ctx} {α : Explicit.Ty}
     → Explicit.Tm Γ α
     → 𝕃.⌊ Γ ⌋ᶜ ⊢ `M 𝕃.⌊ α ⌋ᵗ
⌊ Explicit.` x                      ⌋ᵉ = `return (` (∈ᴸ⇒∈ᴸ-map 𝕃.⌊_⌋ᵗ x))
⌊ Explicit.`let t₁ `in t₂           ⌋ᵉ = ⌊ t₁ ⌋ᵉ `>>= ⌊ t₂ ⌋ᵉ
⌊ Explicit.`false                   ⌋ᵉ = `return `false
⌊ Explicit.`true                    ⌋ᵉ = `return `true
⌊ Explicit.`if t₁ `then t₂ `else t₃ ⌋ᵉ =
  ⌊ t₁ ⌋ᵉ `>>= (`if (` zeroᵛ) `then weaken ⌊ t₂ ⌋ᵉ `else weaken ⌊ t₃ ⌋ᵉ)
⌊ Explicit.`[]                      ⌋ᵉ = `return `[]
⌊ t₁ Explicit.`∷ t₂                 ⌋ᵉ =
  ⌊ t₁ ⌋ᵉ `>>= weaken ⌊ t₂ ⌋ᵉ `>>= `return (` (sucᵛ zeroᵛ) `∷ ` zeroᵛ)
⌊ Explicit.`foldr t₁ t₂ t₃          ⌋ᵉ =
  ⌊ t₃ ⌋ᵉ `>>= `foldrM (subsume₂ ⌊ t₁ ⌋ᵉ) (weaken ⌊ t₂ ⌋ᵉ) (` zeroᵛ)
⌊ Explicit.`tick t                  ⌋ᵉ = `tick ⌊ t ⌋ᵉ
⌊ Explicit.`lazy t                  ⌋ᵉ = `lazily ⌊ t ⌋ᵉ
⌊ Explicit.`force t                 ⌋ᵉ = `forced ⌊ t ⌋ᵉ

⟦⌊_⌋⟧ᵉ : {Γ : Explicit.Ctx} {α : Explicit.Ty}
       → Explicit.Tm Γ α
       → 𝕃.⟦⌊ Γ ⌋⟧ᶜ → Tick 𝕃.⟦⌊ α ⌋⟧ᵗ → Type
⟦⌊ t ⌋⟧ᵉ = ⟦ ⌊ t ⌋ᵉ ⟧ᵉ
