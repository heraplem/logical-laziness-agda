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
import LogicalLaziness.Base.Data.List.All
  as All
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

⌊_⌋≤ᵗ : ∀ {α} {v₁ v₂ : ℂ.⟦ α ⟧ᵗ} → v₁ ℂ.≤ᵗ v₂ → ⌊ v₁ ⌋ᵗ ≲ᵗ ⌊ v₂ ⌋ᵗ
⌊ ℂ.undefined ⌋≤ᵗ = undefined
⌊ ℂ.thunk ψ   ⌋≤ᵗ = thunk ⌊ ψ ⌋≤ᵗ
⌊ ℂ.false     ⌋≤ᵗ = false
⌊ ℂ.true      ⌋≤ᵗ = true
⌊ ℂ.[]        ⌋≤ᵗ = []
⌊ ψ₁ ℂ.∷ ψ₂   ⌋≤ᵗ = ⌊ ψ₁ ⌋≤ᵗ ∷ ⌊ ψ₂ ⌋≤ᵗ

⟦_⟧⌈_⌉ᵗ : (α : Explicit.Ty) → 𝕃.⟦⌊ α ⌋⟧ᵗ → ℂ.⟦ α ⟧ᵗ
⟦ `Bool   ⟧⌈ false     ⌉ᵗ = false
⟦ `Bool   ⟧⌈ true      ⌉ᵗ = true
⟦ `T α    ⟧⌈ undefined ⌉ᵗ = undefined
⟦ `T α    ⟧⌈ thunk v   ⌉ᵗ = thunk ⟦ α ⟧⌈ v ⌉ᵗ
⟦ `List α ⟧⌈ []        ⌉ᵗ = []
⟦ `List α ⟧⌈ v ∷ vs    ⌉ᵗ = ⟦ α ⟧⌈ v ⌉ᵗ ∷ ⟦ `T (`List α) ⟧⌈ vs ⌉ᵗ

⌈_⌉ᵗ : ∀ {α} → 𝕃.⟦⌊ α ⌋⟧ᵗ → ℂ.⟦ α ⟧ᵗ
⌈_⌉ᵗ = ⟦ _ ⟧⌈_⌉ᵗ

⌈_⌉≤ᵗ : ∀ {α} {v₁ v₂ : ℂ.⟦ α ⟧ᵗ} → ⌊ v₁ ⌋ᵗ ≲ᵗ ⌊ v₂ ⌋ᵗ → v₁ ℂ.≤ᵗ v₂
⌈_⌉≤ᵗ {`Bool  } {false    } {false  } false     = ℂ.false
⌈_⌉≤ᵗ {`Bool  } {true     } {true   } true      = ℂ.true
⌈_⌉≤ᵗ {`T α   } {undefined} {_      } undefined = ℂ.undefined
⌈_⌉≤ᵗ {`T α   } {thunk _  } {thunk _} (thunk ψ) = ℂ.thunk ⌈ ψ ⌉≤ᵗ
⌈_⌉≤ᵗ {`List α} {[]       } {[]     } []        = ℂ.[]
⌈_⌉≤ᵗ {`List α} {_ ∷ _    } {_ ∷ _  } (ψ₁ ∷ ψ₂) = ⌈ ψ₁ ⌉≤ᵗ ℂ.∷ ⌈ ψ₂ ⌉≤ᵗ

⌊⌈_⌉⌋ᵗ : ∀ {α} (v : 𝕃.⟦⌊ α ⌋⟧ᵗ) → ⌊ ⌈ v ⌉ᵗ ⌋ᵗ ≡ v
⌊⌈_⌉⌋ᵗ {`Bool   } false     = refl
⌊⌈_⌉⌋ᵗ {`Bool   } true      = refl
⌊⌈_⌉⌋ᵗ {`T α    } undefined = refl
⌊⌈_⌉⌋ᵗ {`T α    } (thunk v) = cong thunk ⌊⌈ v ⌉⌋ᵗ
⌊⌈_⌉⌋ᵗ {`List α } []        = refl
⌊⌈_⌉⌋ᵗ {`List α } (v ∷ vs)  = cong₂ _∷_ ⌊⌈ v ⌉⌋ᵗ ⌊⌈ vs ⌉⌋ᵗ

-- Convert evaluation contexts

⟦_⟧⌊_⌋ᶜ : (Γ : Explicit.Ctx) → ℂ.⟦ Γ ⟧ᶜ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⟦ Γ ⟧⌊ γ ⌋ᶜ = All.gmap⁺ ⟦ _ ⟧⌊_⌋ᵗ γ

⌊_⌋ᶜ : {Γ : Explicit.Ctx} → ℂ.⟦ Γ ⟧ᶜ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⌊ γ ⌋ᶜ = ⟦ _ ⟧⌊ γ ⌋ᶜ

⌊_⌋≤ᶜ : ∀ {Γ} {γ₁ γ₂ : ℂ.⟦ Γ ⟧ᶜ} → γ₁ ℂ.≤ᶜ γ₂ → ⌊ γ₁ ⌋ᶜ ≲ᶜ ⌊ γ₂ ⌋ᶜ
⌊ ∅             ⌋≤ᶜ = ∅
⌊ γ₁≤γ₂ ⸴ v₁≤v₂ ⌋≤ᶜ = ⌊ γ₁≤γ₂ ⌋≤ᶜ ⸴ ⌊ v₁≤v₂ ⌋≤ᵗ

⟦_⟧⌈_⌉ᶜ : (Γ : Explicit.Ctx) → 𝕃.⟦⌊ Γ ⌋⟧ᶜ → ℂ.⟦ Γ ⟧ᶜ
⟦ Γ ⟧⌈ γ ⌉ᶜ = All.gmap⁻ ⟦ _ ⟧⌈_⌉ᵗ γ

⌈_⌉ᶜ : {Γ : Explicit.Ctx} → 𝕃.⟦⌊ Γ ⌋⟧ᶜ → ℂ.⟦ Γ ⟧ᶜ
⌈ γ ⌉ᶜ = ⟦ _ ⟧⌈ γ ⌉ᶜ

⌈_⌉≤ᶜ : ∀ {Γ} {γ₁ γ₂ : ℂ.⟦ Γ ⟧ᶜ} → ⌊ γ₁ ⌋ᶜ ≲ᶜ ⌊ γ₂ ⌋ᶜ → γ₁ ℂ.≤ᶜ γ₂
⌈_⌉≤ᶜ {γ₁ = ∅    } {γ₂ = ∅    } ∅                       = ∅
⌈_⌉≤ᶜ {γ₁ = _ ⸴ _} {γ₂ = _ ⸴ _} (⌊γ₁⌋≤⌊γ₂⌋ ⸴ ⌊v₁⌋≤⌊v₂⌋) = ⌈ ⌊γ₁⌋≤⌊γ₂⌋ ⌉≤ᶜ ⸴ ⌈ ⌊v₁⌋≤⌊v₂⌋ ⌉≤ᵗ

open import Data.List.Relation.Unary.All as All
⌊⌈_⌉⌋ᶜ : ∀ {Γ} (γ : 𝕃.⟦⌊ Γ ⌋⟧ᶜ) → ⌊ ⌈ γ ⌉ᶜ ⌋ᶜ ≡ γ
⌊⌈_⌉⌋ᶜ {∅} ∅ = refl
⌊⌈_⌉⌋ᶜ {Γ = _ ⸴ _} (γ ⸴ v) = cong₂ _⸴_ (All.map⁺-map⁻ ⌈_⌉ᵗ ⌊_⌋ᵗ ⌊⌈_⌉⌋ᵗ γ) ⌊⌈ v ⌉⌋ᵗ

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
