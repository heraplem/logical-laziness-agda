module LogicalLaziness.Language.Logic.Renaming where

open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.All
  as All
open import Data.List.Membership.Propositional.Properties

open import LogicalLaziness.Base
import LogicalLaziness.Base.Data.List.All
  as All
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Language.Logic.Base

---------------
-- Renamings --
---------------

infix 2 _→ʳ_
_→ʳ_ : Ctx → Ctx → Type
Γ →ʳ Δ = ∀ {α} → α ∈ᴸ Γ → α ∈ᴸ Δ

variable
  ρ : Γ →ʳ Δ

↑ʳ_ : Γ →ʳ Δ → Γ ⸴ α →ʳ Δ ⸴ α
↑ʳ_ ρ zeroᵛ    = zeroᵛ
↑ʳ_ ρ (sucᵛ x) = sucᵛ (ρ x)

-- Apply a renaming to a term.
infixr -1 _$ʳ_
_$ʳ_ : Γ →ʳ Δ → Γ ⊢ α → Δ ⊢ α
ρ $ʳ ` x                      = ` ρ x
ρ $ʳ `let t₁ `in t₂           = `let (ρ $ʳ t₁) `in (↑ʳ ρ $ʳ t₂)
ρ $ʳ `tt                      = `tt
ρ $ʳ `false                   = `false
ρ $ʳ `true                    = `true
ρ $ʳ `if t₁ `then t₂ `else t₃ = `if (ρ $ʳ t₁) `then ρ $ʳ t₂ `else (ρ $ʳ t₃)
ρ $ʳ t₁ `≟ t₂                 = (ρ $ʳ t₁) `≟ (ρ $ʳ t₂)
ρ $ʳ t₁ `≲ t₂                 = (ρ $ʳ t₁) `≲ (ρ $ʳ t₂)
ρ $ʳ t₁ `, t₂                 = (ρ $ʳ t₁) `, (ρ $ʳ t₂)
ρ $ʳ `proj₁ t₁                = `proj₁ (ρ $ʳ t₁)
ρ $ʳ `proj₂ t₁                = `proj₂ (ρ $ʳ t₁)
ρ $ʳ `undefined               = `undefined
ρ $ʳ `thunk t₁                = `thunk (ρ $ʳ t₁)
ρ $ʳ `T-case t₁ t₂ t₃         = `T-case (ρ $ʳ t₁) (↑ʳ ρ $ʳ t₂) (ρ $ʳ t₃)
ρ $ʳ # x                      = # x
ρ $ʳ t₁ `+ t₂                 = (ρ $ʳ t₁) `+ (ρ $ʳ t₂)
ρ $ʳ `[]                      = `[]
ρ $ʳ t₁ `∷ t₂                 = (ρ $ʳ t₁) `∷ (ρ $ʳ t₂)
ρ $ʳ `foldrA t₁ t₂ t₃         = `foldrA (↑ʳ ↑ʳ ρ $ʳ t₁) (ρ $ʳ t₂) (ρ $ʳ t₃)
ρ $ʳ `free                    = `free
ρ $ʳ t₁ `? t₂                 = (ρ $ʳ t₁) `? (ρ $ʳ t₂)
ρ $ʳ `fail                    = `fail

-- Weakening

weakenʳ : Γ →ʳ Γ ⸴ τ
weakenʳ = sucᵛ

weaken : Γ ⊢ α → Γ ⸴ τ ⊢ α
weaken t = weakenʳ $ʳ t

-- Generalized weakening on the right

gweakenrʳ : Γ →ʳ Γ …⸴ Δ
gweakenrʳ = ∈-++⁺ʳ _

gweakenr : Γ ⊢ α → Γ …⸴ Δ ⊢ α
gweakenr = gweakenrʳ $ʳ_

-- Generalized weakening on the left

gweakenlʳ : Γ →ʳ Δ …⸴ Γ
gweakenlʳ = ∈-++⁺ˡ

gweakenl : Γ ⊢ α → Δ …⸴ Γ ⊢ α
gweakenl = gweakenlʳ $ʳ_

-- Exchange

exchangeʳ : Γ ⸴ τ₁ ⸴ τ₂ →ʳ Γ ⸴ τ₂ ⸴ τ₁
exchangeʳ zeroᵛ           = sucᵛ zeroᵛ
exchangeʳ (sucᵛ zeroᵛ)    = zeroᵛ
exchangeʳ (sucᵛ (sucᵛ x)) = sucᵛ (sucᵛ x)

exchange : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
exchange = exchangeʳ $ʳ_

-- A common special-case context manipulation

subsumeʳ : Γ ⸴ τ₁ →ʳ Γ ⸴ τ₂ ⸴ τ₁
subsumeʳ zeroᵛ    = zeroᵛ
subsumeʳ (sucᵛ x) = sucᵛ (sucᵛ x)

subsume : Γ ⸴ τ₁ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
subsume t = subsumeʳ $ʳ t

-- An uncommon special-case context manipulation

subsume₂ʳ : Γ ⸴ τ₁ ⸴ τ₂ →ʳ Γ ⸴ τ₃ ⸴ τ₁ ⸴ τ₂
subsume₂ʳ zeroᵛ           = zeroᵛ
subsume₂ʳ (sucᵛ zeroᵛ)    = sucᵛ zeroᵛ
subsume₂ʳ (sucᵛ (sucᵛ x)) = sucᵛ (sucᵛ (sucᵛ x))

subsume₂ : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α → Γ ⸴ τ₃ ⸴ τ₁ ⸴ τ₂ ⊢ α
subsume₂ t = subsume₂ʳ $ʳ t

---------------------------------
-- Context manipulation lemmas --
---------------------------------

-- Expresses the proposition that a renaming ρ embeds an environment γ into an
-- environment δ.
infix 4 _ʳ_⊑_
_ʳ_⊑_ : Γ →ʳ Δ → ⟦ Γ ⟧ᶜ → ⟦ Δ ⟧ᶜ → Type
_ʳ_⊑_ {Γ = Γ} ρ γ δ = (∀ {α} (x : α ∈ᴸ Γ) → All.lookup δ (ρ x) ≡ All.lookup γ x)

-- A weakened embedding is again an embedding.
⊑⇒⊑-↑ʳ : ρ ʳ γ ⊑ δ
       → ∀ {α} {v : ⟦ α ⟧ᵗ} → ↑ʳ ρ ʳ γ ⸴ v ⊑ δ ⸴ v
⊑⇒⊑-↑ʳ η zeroᵛ    = refl
⊑⇒⊑-↑ʳ η (sucᵛ x) = η x

⊑⇒⊑-↑↑ʳ : ∀ {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ}
        → ρ ʳ γ ⊑ δ
        → ↑ʳ ↑ʳ ρ ʳ γ ⸴ v₁ ⸴ v₂ ⊑ δ ⸴ v₁ ⸴ v₂
⊑⇒⊑-↑↑ʳ η x = ⊑⇒⊑-↑ʳ (⊑⇒⊑-↑ʳ η) x

weakenʳ-⊑ : ∀ {v : ⟦ τ ⟧ᵗ} → weakenʳ ʳ γ ⊑ γ ⸴ v
weakenʳ-⊑ _ = refl

gweakenrʳ-⊑ : {γ : ⟦ Γ ⟧ᶜ} (δ : ⟦ Δ ⟧ᶜ) → gweakenrʳ ʳ γ ⊑ (γ …⸴′ δ)
gweakenrʳ-⊑ {Γ = Γ} {Δ = Δ} {γ = γ} δ = All.lookup-++ʳ {pxs = δ} {pys = γ}

gweakenlʳ-⊑ : (γ : ⟦ Γ ⟧ᶜ) {δ : ⟦ Δ ⟧ᶜ} → gweakenlʳ ʳ γ ⊑ (δ …⸴′ γ)
gweakenlʳ-⊑ {Γ = Γ} {Δ = Δ} γ {δ} = All.lookup-++ˡ {pxs = γ} {pys = δ}

exchangeʳ-⊑ : ∀ {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ}
            → exchangeʳ ʳ γ ⸴ v₁ ⸴ v₂ ⊑ γ ⸴ v₂ ⸴ v₁
exchangeʳ-⊑ zeroᵛ           = refl
exchangeʳ-⊑ (sucᵛ zeroᵛ)    = refl
exchangeʳ-⊑ (sucᵛ (sucᵛ x)) = refl

subsumeʳ-⊑ : ∀ {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ}
           → subsumeʳ ʳ γ ⸴ v₁ ⊑ γ ⸴ v₂ ⸴ v₁
subsumeʳ-⊑ zeroᵛ    = refl
subsumeʳ-⊑ (sucᵛ x) = refl

subsume₂ʳ-⊑ : ∀ {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v₃ : ⟦ τ₃ ⟧ᵗ}
            → subsume₂ʳ ʳ γ ⸴ v₁ ⸴ v₂ ⊑ γ ⸴ v₃ ⸴ v₁ ⸴ v₂
subsume₂ʳ-⊑ zeroᵛ           = refl
subsume₂ʳ-⊑ (sucᵛ zeroᵛ)    = refl
subsume₂ʳ-⊑ (sucᵛ (sucᵛ x)) = refl

mutual

  -- Embedding a renaming preserves semantics.
  ⇓ʳ : ρ ʳ γ ⊑ δ
     → ∀ {v} {t : Γ ⊢ α}
     → ⟦ t ⟧ᵉ γ ∋ v
     → ⟦ ρ $ʳ t ⟧ᵉ δ ∋ v
  ⇓ʳ {ρ = ρ} {δ = δ} η (⇓ x)                     = subst (⟦ ` ρ x ⟧ᵉ δ ∋_) (η x) (⇓ ρ x)
  ⇓ʳ                 η (⇓let φ₁ ⇓in φ₂)          = ⇓let ⇓ʳ η φ₁ ⇓in ⇓ʳ (⊑⇒⊑-↑ʳ η) φ₂
  ⇓ʳ                 η ⇓tt                       = ⇓tt
  ⇓ʳ                 η ⇓false                    = ⇓false
  ⇓ʳ                 η ⇓true                     = ⇓true
  ⇓ʳ                 η (⇓if φ₁ ⇓else φ₂)         = ⇓if ⇓ʳ η φ₁ ⇓else ⇓ʳ η φ₂
  ⇓ʳ                 η (⇓if φ₁ ⇓then φ₂)         = ⇓if ⇓ʳ η φ₁ ⇓then ⇓ʳ η φ₂
  ⇓ʳ                 η (⇓≟-true φ₁ φ₂)           = ⇓≟-true (⇓ʳ η φ₁) (⇓ʳ η φ₂)
  ⇓ʳ                 η (⇓≟-false φ₁ φ₂ ψ)        = ⇓≟-false (⇓ʳ η φ₁) (⇓ʳ η φ₂) ψ
  ⇓ʳ                 η (⇓≲-true φ₁ φ₂ ψ)         = ⇓≲-true (⇓ʳ η φ₁) (⇓ʳ η φ₂) ψ
  ⇓ʳ                 η (⇓≲-false φ₁ φ₂ ψ)        = ⇓≲-false (⇓ʳ η φ₁) (⇓ʳ η φ₂) ψ
  ⇓ʳ                 η (φ₁ ⇓, φ₂)                = ⇓ʳ η φ₁ ⇓, ⇓ʳ η φ₂
  ⇓ʳ                 η (⇓proj₁ φ)                = ⇓proj₁ (⇓ʳ η φ)
  ⇓ʳ                 η (⇓proj₂ φ)                = ⇓proj₂ (⇓ʳ η φ)
  ⇓ʳ                 η ⇓undefined                = ⇓undefined
  ⇓ʳ                 η (⇓thunk φ)                = ⇓thunk (⇓ʳ η φ)
  ⇓ʳ                 η (⇓T-case-undefined φ₁ φ₂) = ⇓T-case-undefined (⇓ʳ η φ₁) (⇓ʳ η φ₂)
  ⇓ʳ                 η (⇓T-case-thunk φ₁ φ₂)     = ⇓T-case-thunk (⇓ʳ η φ₁) (⇓ʳ (⊑⇒⊑-↑ʳ η) φ₂)
  ⇓ʳ                 η (⇓# n)                    = ⇓# n
  ⇓ʳ                 η (φ₁ ⇓+ φ₂)                = ⇓ʳ η φ₁ ⇓+ ⇓ʳ η φ₂
  ⇓ʳ                 η ⇓[]                       = ⇓[]
  ⇓ʳ                 η (φ₁ ⇓∷ φ₂)                = ⇓ʳ η φ₁ ⇓∷ ⇓ʳ η φ₂
  ⇓ʳ                 η (⇓foldrA φ₁ φ₂)           = ⇓foldrA (⇓ʳ η φ₁) (⇓foldrA-↑↑ʳ η φ₂)
  ⇓ʳ                 η ⇓free                     = ⇓free
  ⇓ʳ                 η (⇓?ˡ φ)                   = ⇓?ˡ (⇓ʳ η φ)
  ⇓ʳ                 η (⇓?ʳ φ)                   = ⇓?ʳ (⇓ʳ η φ)

  ⇓foldrA-↑↑ʳ : ρ ʳ γ ⊑ δ
              → ∀ {b as}
              → ⟦foldrA t₁ , t₂ ⟧ᵉ γ as ∋ b
              → ⟦foldrA (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ as ∋ b
  ⇓foldrA-↑↑ʳ η (⇓foldrA-[] φ)    = ⇓foldrA-[] (⇓ʳ η φ)
  ⇓foldrA-↑↑ʳ η (⇓foldrA-∷ φ₁ φ₂) =
    ⇓foldrA-∷
      (⇓foldrA′-↑↑ʳ η φ₁)
      (⇓ʳ (⊑⇒⊑-↑↑ʳ η) φ₂)

  ⇓foldrA′-↑↑ʳ : ρ ʳ γ ⊑ δ
               → ∀ {v xsT}
               → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ xsT ∋ v
               → ⟦foldrA′ (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ xsT ∋ v
  ⇓foldrA′-↑↑ʳ η ⇓foldrA-undefined = ⇓foldrA-undefined
  ⇓foldrA′-↑↑ʳ η (⇓foldrA-thunk φ) = ⇓foldrA-thunk (⇓foldrA-↑↑ʳ η φ)

⇓weaken : {v₁ : ⟦ τ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
        → ⟦ t ⟧ᵉ γ ∋ v
        → ⟦ weaken t ⟧ᵉ (γ ⸴ v₁) ∋ v
⇓weaken {γ = γ} {v = v₁} φ = ⇓ʳ (weakenʳ-⊑ {γ = γ} {v = v₁}) φ

⇓gweakenr : ∀ {γ : ⟦ Γ ⟧ᶜ} (δ : ⟦ Δ ⟧ᶜ) {v}
          → ⟦ t ⟧ᵉ γ ∋ v
          → ⟦ gweakenr t ⟧ᵉ (γ …⸴′ δ) ∋ v
⇓gweakenr δ = ⇓ʳ (gweakenrʳ-⊑ δ)

⇓gweakenl : ∀ (γ : ⟦ Γ ⟧ᶜ) {δ : ⟦ Δ ⟧ᶜ} {v}
          → ⟦ t ⟧ᵉ γ ∋ v
          → ⟦ gweakenl t ⟧ᵉ (δ …⸴′ γ) ∋ v
⇓gweakenl γ = ⇓ʳ (gweakenlʳ-⊑ γ)

⇓exchange : {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
          → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ v
          → ⟦ exchange t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ v
⇓exchange = ⇓ʳ exchangeʳ-⊑

⇓subsume : {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
         → ⟦ t ⟧ᵉ (γ ⸴ v₁) ∋ v
         → ⟦ subsume t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ v
⇓subsume = ⇓ʳ subsumeʳ-⊑

⇓subsume₂ : ∀ {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v₃ : ⟦ τ₃ ⟧ᵗ} {v}
          → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ v
          → ⟦ subsume₂ t ⟧ᵉ (γ ⸴ v₃ ⸴ v₁ ⸴ v₂) ∋ v
⇓subsume₂ = ⇓ʳ subsume₂ʳ-⊑

-- Now we invert the above.

mutual

  ⇑ʳ : ρ ʳ γ ⊑ δ
     → ∀ {v : ⟦ α ⟧ᵗ}
     → ⟦ ρ $ʳ t ⟧ᵉ δ ∋ v
     → ⟦ t ⟧ᵉ γ ∋ v
  ⇑ʳ {t = ` x                      } η (⇓ _)                     = subst (⟦ ` x ⟧ᵉ _ ∋_) (sym (η x)) (⇓ x)
  ⇑ʳ {t = `let t₁ `in t₂           } η (⇓let φ₁ ⇓in φ₂)          = ⇓let (⇑ʳ η φ₁) ⇓in (⇑ʳ (⊑⇒⊑-↑ʳ η) φ₂)
  ⇑ʳ {t = `tt                      } η ⇓tt                       = ⇓tt
  ⇑ʳ {t = `false                   } η ⇓false                    = ⇓false
  ⇑ʳ {t = `true                    } η ⇓true                     = ⇓true
  ⇑ʳ {t = `if t₁ `then t₂ `else t₃ } η (⇓if φ₁ ⇓else φ₂)         = ⇓if ⇑ʳ η φ₁ ⇓else ⇑ʳ η φ₂
  ⇑ʳ {t = `if t₁ `then t₂ `else t₃ } η (⇓if φ₁ ⇓then φ₂)         = ⇓if ⇑ʳ η φ₁ ⇓then ⇑ʳ η φ₂
  ⇑ʳ {t = t₁ `≟ t₂                 } η (⇓≟-true φ₁ φ₂)           = ⇓≟-true (⇑ʳ η φ₁) (⇑ʳ η φ₂)
  ⇑ʳ {t = t₁ `≟ t₂                 } η (⇓≟-false φ₁ φ₂ ψ)        = ⇓≟-false (⇑ʳ η φ₁) (⇑ʳ η φ₂) ψ
  ⇑ʳ {t = t₁ `≲ t₂                 } η (⇓≲-true φ₁ φ₂ ψ)         = ⇓≲-true (⇑ʳ η φ₁) (⇑ʳ η φ₂) ψ
  ⇑ʳ {t = t₁ `≲ t₂                 } η (⇓≲-false φ₁ φ₂ ψ)        = ⇓≲-false (⇑ʳ η φ₁) (⇑ʳ η φ₂) ψ
  ⇑ʳ {t = t₁ `, t₂                 } η (φ₁ ⇓, φ₂)                = ⇑ʳ η φ₁ ⇓, ⇑ʳ η φ₂
  ⇑ʳ {t = `proj₁ t                 } η (⇓proj₁ φ)                = ⇓proj₁ (⇑ʳ η φ)
  ⇑ʳ {t = `proj₂ t                 } η (⇓proj₂ φ)                = ⇓proj₂ (⇑ʳ η φ)
  ⇑ʳ {t = `undefined               } η ⇓undefined                = ⇓undefined
  ⇑ʳ {t = `thunk t                 } η (⇓thunk φ)                = ⇓thunk (⇑ʳ η φ)
  ⇑ʳ {t = `T-case t t₁ t₂          } η (⇓T-case-undefined φ₁ φ₂) = ⇓T-case-undefined (⇑ʳ η φ₁) (⇑ʳ η φ₂)
  ⇑ʳ {t = `T-case t t₁ t₂          } η (⇓T-case-thunk φ₁ φ₂)     = ⇓T-case-thunk (⇑ʳ η φ₁) (⇑ʳ (λ{ zeroᵛ → refl ; (sucᵛ x) → η x }) φ₂)
  ⇑ʳ {t = # x                      } η (⇓# n)                    = ⇓# x
  ⇑ʳ {t = t₁ `+ t₂                 } η (φ₁ ⇓+ φ₂)                = ⇑ʳ η φ₁ ⇓+ ⇑ʳ η φ₂
  ⇑ʳ {t = `[]                      } η ⇓[]                       = ⇓[]
  ⇑ʳ {t = t₁ `∷ t₂                 } η (φ₁ ⇓∷ φ₂)                = ⇑ʳ η φ₁ ⇓∷ ⇑ʳ η φ₂
  ⇑ʳ {t = `foldrA t₁ t₂ t₃         } η (⇓foldrA φ₁ φ₂)           = ⇓foldrA (⇑ʳ η φ₁) (⇑foldrA-↑↑ʳ η φ₂)
  ⇑ʳ {t = `free                    } η ⇓free                     = ⇓free
  ⇑ʳ {t = t₁ `? t₂                 } η (⇓?ˡ φ)                   = ⇓?ˡ (⇑ʳ η φ)
  ⇑ʳ {t = t₁ `? t₂                 } η (⇓?ʳ φ)                   = ⇓?ʳ (⇑ʳ η φ)

  ⇑foldrA-↑↑ʳ : ρ ʳ γ ⊑ δ
              → ∀ {v xs}
              → ⟦foldrA (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ xs ∋ v
              → ⟦foldrA t₁ , t₂ ⟧ᵉ γ xs ∋ v
  ⇑foldrA-↑↑ʳ η (⇓foldrA-[] φ)    = ⇓foldrA-[] (⇑ʳ η φ)
  ⇑foldrA-↑↑ʳ η (⇓foldrA-∷ φ₁ φ₂) =
    ⇓foldrA-∷
      (⇑foldrA′-↑↑ʳ η φ₁)
      (⇑ʳ (⊑⇒⊑-↑↑ʳ η) φ₂)

  ⇑foldrA′-↑↑ʳ : ρ ʳ γ ⊑ δ
               → ∀ {v xsT}
               → ⟦foldrA′ (↑ʳ ↑ʳ ρ) $ʳ t₁ , ρ $ʳ t₂ ⟧ᵉ δ xsT ∋ v
               → ⟦foldrA′ t₁ , t₂ ⟧ᵉ γ xsT ∋ v
  ⇑foldrA′-↑↑ʳ η ⇓foldrA-undefined = ⇓foldrA-undefined
  ⇑foldrA′-↑↑ʳ η (⇓foldrA-thunk φ) = ⇓foldrA-thunk (⇑foldrA-↑↑ʳ η φ)

⇑weaken :
  ∀ {Γ α τ} {t : Γ ⊢ τ} {γ : ⟦ Γ ⟧ᶜ} {a : ⟦ α ⟧ᵗ}
    {v : ⟦ τ ⟧ᵗ}
  → ⟦ weaken t ⟧ᵉ (γ ⸴ a) ∋ v
  → ⟦ t ⟧ᵉ γ ∋ v
⇑weaken {γ = γ} {v = v₁} φ = ⇑ʳ (weakenʳ-⊑ {γ = γ} {v = v₁}) φ

⇑gweakenr : ∀ {γ : ⟦ Γ ⟧ᶜ} (δ : ⟦ Δ ⟧ᶜ) {v}
          → ⟦ gweakenr t ⟧ᵉ (γ …⸴′ δ) ∋ v
          → ⟦ t ⟧ᵉ γ ∋ v
⇑gweakenr δ = ⇑ʳ (gweakenrʳ-⊑ δ)

⇑gweakenl : ∀ (γ : ⟦ Γ ⟧ᶜ) {δ : ⟦ Δ ⟧ᶜ} {v}
          → ⟦ gweakenl t ⟧ᵉ (δ …⸴′ γ) ∋ v
          → ⟦ t ⟧ᵉ γ ∋ v
⇑gweakenl γ = ⇑ʳ (gweakenlʳ-⊑ γ)

⇑exchange : {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
          → ⟦ exchange t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ v
          → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ v
⇑exchange = ⇑ʳ exchangeʳ-⊑

⇑subsume : ∀ {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v}
         → ⟦ subsume t ⟧ᵉ (γ ⸴ v₂ ⸴ v₁) ∋ v
         → ⟦ t ⟧ᵉ (γ ⸴ v₁) ∋ v
⇑subsume = ⇑ʳ subsumeʳ-⊑

⇑subsume₂ : ∀ {v₁ : ⟦ τ₁ ⟧ᵗ} {v₂ : ⟦ τ₂ ⟧ᵗ} {v₃ : ⟦ τ₃ ⟧ᵗ} {v}
          → ⟦ subsume₂ t ⟧ᵉ (γ ⸴ v₃ ⸴ v₁ ⸴ v₂) ∋ v
          → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ v₂) ∋ v
⇑subsume₂ = ⇑ʳ subsume₂ʳ-⊑
