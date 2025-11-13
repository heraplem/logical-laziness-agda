module LogicalLaziness.Language.Logic.Construct where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Product.Properties
open import Data.Nat
open import Data.Nat.Properties

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Effect.Monad.Tick
open import LogicalLaziness.Base.Data.T
open import LogicalLaziness.Base.Data.ListA
open import LogicalLaziness.Language.Logic.Base
open import LogicalLaziness.Language.Logic.Renaming

-------------------------------
-- Object-language writer monad
-------------------------------

infixr 1.51 _`>>=_

`M : Ty → Ty
`M α = α `× `ℕ

variable
  c c₁ c₂ : ℕ

⇓cost≡ : ∀ {v} → c₁ ≡ c₂ → ⟦ t ⟧ᵉ γ ∋ (v , c₁) → ⟦ t ⟧ᵉ γ ∋ (v , c₂)
⇓cost≡ refl φ = φ

⇓[cost+0] : ∀ {v} → ⟦ t ⟧ᵉ γ ∋ (v , c + 0) → ⟦ t ⟧ᵉ γ ∋ (v , c)
⇓[cost+0] φ = ⇓cost≡ (+-identityʳ _) φ

⇑[cost+0] : ∀ {v} → ⟦ t ⟧ᵉ γ ∋ (v , c) → ⟦ t ⟧ᵉ γ ∋ (v , c + 0)
⇑[cost+0] φ = ⇓cost≡ (sym (+-identityʳ _)) φ

_`>>=_ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → Γ ⊢ `M β
t₁ `>>= t₂ =
  `let t₁ `in
  `let (`let `proj₁ (` zeroᵛ) `in subsume t₂) `in
  (`proj₁ (` zeroᵛ) `, (`proj₂ (` (sucᵛ zeroᵛ)) `+ `proj₂ (` zeroᵛ)))

data ⟦>>=_,_⟧ᵉ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → ⟦ Γ ⟧ᶜ → Tick ⟦ β ⟧ᵗ → Type where
  ⇓>>=-intro : ∀ {a b c₁ c₂}
               → ⟦ t₁ ⟧ᵉ γ ∋ (a , c₁)
               → ⟦ t₂ ⟧ᵉ (γ ⸴ a) ∋ (b , c₂)
               → ⟦>>= t₁ , t₂ ⟧ᵉ γ ∋ (b , c₁ + c₂)

⇓>>= : ∀ {u} → ⟦>>= t₁ , t₂ ⟧ᵉ γ u → ⟦ t₁ `>>= t₂ ⟧ᵉ γ u
⇓>>= (⇓>>=-intro φ₁ φ₂) =
  ⇓let φ₁ ⇓in
  ⇓let (⇓let ⇓proj₁ (⇓ zeroᵛ) ⇓in ⇓subsume φ₂) ⇓in
  ⇓proj₁ (⇓ zeroᵛ) ⇓, ⇓proj₂ (⇓ sucᵛ zeroᵛ) ⇓+ ⇓proj₂ (⇓ zeroᵛ)

⇑>>= : ∀ {u} → ⟦ t₁ `>>= t₂ ⟧ᵉ γ u → ⟦>>= t₁ , t₂ ⟧ᵉ γ u
⇑>>= (⇓let φ₁ ⇓in
      ⇓let (⇓let ⇓proj₁ (⇓ _) ⇓in φ₂) ⇓in
      ⇓proj₁ (⇓ .zeroᵛ) ⇓, (⇓proj₂ (⇓ sucᵛ zeroᵛ) ⇓+ ⇓proj₂ (⇓ zeroᵛ))) =
  ⇓>>=-intro φ₁ (⇑subsume φ₂)

`return : Γ ⊢ α → Γ ⊢ `M α
`return t = t `, 0

-- `return is purely structural, so we don't need to prove an inversion lemma
pattern ⇓return φ = φ ⇓, ⇓# 0

`tick : Γ ⊢ `M α → Γ ⊢ `M α
`tick t = `let t `in `proj₁ (` zeroᵛ) `, 1 `+ `proj₂ (` zeroᵛ)

pattern ⇓tick φ = ⇓let φ ⇓in ⇓proj₁ (⇓ zeroᵛ) ⇓, ⇓# 1 ⇓+ ⇓proj₂ (⇓ zeroᵛ)

-- Transpose T and M

`transposeM : Γ ⊢ `T (`M α) → Γ ⊢ `M (`T α)
`transposeM t = `T-case t (` zeroᵛ `>>= `return (`thunk (` zeroᵛ))) (`return `undefined)

data ⟦transposeM_⟧ᵉ : Γ ⊢ `T (`M α) → ⟦ Γ ⟧ᶜ → Tick (T ⟦ α ⟧ᵗ) → Type where
  ⇓transposeM-undefined : ⟦ t ⟧ᵉ γ ∋ undefined
                        → ⟦transposeM t ⟧ᵉ γ ∋ (undefined , 0)
  ⇓transposeM-thunk : ∀ {v}
                    → ⟦ t ⟧ᵉ γ ∋ thunk (v , c)
                    → ⟦transposeM t ⟧ᵉ γ ∋ (thunk v , c)

⇓transposeM : ∀ {u} → ⟦transposeM t ⟧ᵉ γ ∋ u → ⟦ `transposeM t ⟧ᵉ γ ∋ u
⇓transposeM (⇓transposeM-undefined φ) = ⇓T-case-undefined φ (⇓undefined ⇓, ⇓# 0)
⇓transposeM (⇓transposeM-thunk φ)     =
  ⇓T-case-thunk φ (⇓[cost+0] (⇓>>= (⇓>>=-intro (⇓ zeroᵛ) (⇓thunk (⇓ zeroᵛ) ⇓, ⇓# 0))))

open import Data.Product.Properties
open import Data.Nat.Properties

⇑transposeM : ∀ {u} → ⟦ `transposeM t ⟧ᵉ γ ∋ u → ⟦transposeM t ⟧ᵉ γ ∋ u
⇑transposeM (⇓T-case-undefined φ₁ (⇓return ⇓undefined)) = ⇓transposeM-undefined φ₁
⇑transposeM {t = t} {γ = γ} (⇓T-case-thunk φ₁ φ₂) with ⇑>>= φ₂
... | ⇓>>=-intro (⇓ _) (⇓return (⇓thunk (⇓ _))) =
  ⇓transposeM-thunk (⇓≡ (cong thunk (×-≡,≡→≡ (refl , sym (+-identityʳ _)))) φ₁)

-- An additional layer of abstraction that makes foldrM and associated proofs
-- easier

`transposeF : Γ ⸴ α ⸴ `T β ⊢ `M β
            → Γ ⸴ α ⸴ `T (`M β) ⊢ `M β
`transposeF t = `transposeM (` zeroᵛ) `>>= subsume t

data ⟦transposeF_⟧ᵉ : Γ ⸴ α ⸴ `T β ⊢ `M β → ⟦ Γ ⸴ α ⸴ `T (`M β) ⟧ᶜ → Tick ⟦ β ⟧ᵗ → Type where
  ⇓transposeF-undefined : ∀ {v u}
                        → ⟦ t ⟧ᵉ (γ ⸴ v ⸴ undefined) ∋ u
                        → ⟦transposeF t ⟧ᵉ (γ ⸴ v ⸴ undefined) ∋ u
  ⇓transposeF-thunk : ∀ {v₁ v₂ v₃ c₁ c₂}
                    → ⟦ t ⟧ᵉ (γ ⸴ v₁ ⸴ thunk v₂) ∋ (v₃ , c₂)
                    → ⟦transposeF t ⟧ᵉ (γ ⸴ v₁ ⸴ thunk (v₂ , c₁)) ∋ (v₃ , c₁ + c₂)

⇓transposeF : ∀ {u} → ⟦transposeF t ⟧ᵉ γ ∋ u → ⟦ `transposeF t ⟧ᵉ γ ∋ u
⇓transposeF (⇓transposeF-undefined φ) =
  ⇓>>=
    (⇓>>=-intro
      (⇓transposeM (⇓transposeM-undefined (⇓ zeroᵛ)))
      (⇓subsume φ))
⇓transposeF (⇓transposeF-thunk φ)     =
  ⇓>>=
    (⇓>>=-intro
      (⇓transposeM (⇓transposeM-thunk (⇓ zeroᵛ)))
      (⇓subsume φ))

⇑transposeF : ∀ {u} → ⟦ `transposeF t ⟧ᵉ γ ∋ u → ⟦transposeF t ⟧ᵉ γ ∋ u
⇑transposeF {γ = _ ⸴ _ ⸴ _} φ
 with ⇑>>= φ
... | ⇓>>=-intro φ₁ φ₂
 with ⇑transposeM φ₁
... | ⇓transposeM-undefined (⇓ _) = ⇓transposeF-undefined (⇑subsume φ₂)
... | ⇓transposeM-thunk (⇓ _)     = ⇓transposeF-thunk (⇑subsume φ₂)

-- Monadic foldr

`foldrM : Γ ⸴ α ⸴ `T β ⊢ `M β
        → Γ ⊢ `M β
        → Γ ⊢ `ListA α
        → Γ ⊢ `M β
`foldrM t₁ t₂ t₃ = `foldrA (`transposeF t₁) t₂ t₃

data ⟦foldrM*_,_⟧ᵉ : Γ ⸴ α ⸴ `T β ⊢ `M β
                   → Γ ⊢ `M β
                   → ⟦ Γ ⟧ᶜ
                   → ListA ⟦ α ⟧ᵗ
                   → ⟦ `M β ⟧ᵗ
                   → Type where
  foldrM*-[] : ∀ {u} →
               ⟦ t₂ ⟧ᵉ γ ∋ u →
               ⟦foldrM* t₁ , t₂ ⟧ᵉ γ [] ∋ u

  foldrM*-undefined : ∀ {a u} →
                      ⟦ t₁ ⟧ᵉ (γ ⸴ a ⸴ undefined) ∋ u →
                      ⟦foldrM* t₁ , t₂ ⟧ᵉ γ (a ∷ undefined) ∋ u

  foldrM*-thunk : ∀ {v₁} {v₂ : ListA ⟦ β ⟧ᵗ} {v₃ v₄ c₁ c₂} →
                  ⟦foldrM* t₁ , t₂ ⟧ᵉ γ v₂ ∋ (v₃ , c₁) →
                  ⟦ t₁ ⟧ᵉ (γ ⸴ v₁ ⸴ thunk v₃) ∋ (v₄ , c₂) →
                  ⟦foldrM* t₁ , t₂ ⟧ᵉ γ (v₁ ∷ thunk v₂) ∋ (v₄ , c₁ + c₂)

data ⟦foldrM_,_,_⟧ᵉ : Γ ⸴ α ⸴ `T β ⊢ `M β
                    → Γ ⊢ `M β
                    → Γ ⊢ `ListA α
                    → ⟦ Γ ⟧ᶜ
                    → ⟦ `M β ⟧ᵗ
                    → Type where
  ⇓foldrM-intro : ∀ {as u}
                → ⟦ t₃ ⟧ᵉ γ ∋ as
                → ⟦foldrM* t₁ , t₂ ⟧ᵉ γ as ∋ u
                → ⟦foldrM t₁ , t₂ , t₃ ⟧ᵉ γ ∋ u

⇓foldrM*⇒⇓foldrA : ∀ {v u}
                 → ⟦foldrM* t₁ , t₂ ⟧ᵉ γ v ∋ u
                 → ⟦foldrA (`transposeF t₁) , t₂ ⟧ᵉ γ v ∋ u
⇓foldrM*⇒⇓foldrA (foldrM*-[] φ) = ⇓foldrA-[] φ
⇓foldrM*⇒⇓foldrA (foldrM*-undefined φ) = ⇓foldrA-∷ ⇓foldrA-undefined (⇓transposeF (⇓transposeF-undefined φ))
⇓foldrM*⇒⇓foldrA (foldrM*-thunk φ₁ φ₂) = ⇓foldrA-∷ (⇓foldrA-thunk (⇓foldrM*⇒⇓foldrA φ₁)) (⇓transposeF (⇓transposeF-thunk φ₂))

⇓foldrA⇒⇓foldrM* : ∀ {v u}
                 → ⟦foldrA (`transposeF t₁) , t₂ ⟧ᵉ γ v ∋ u
                 → ⟦foldrM* t₁ , t₂ ⟧ᵉ γ v ∋ u
⇓foldrA⇒⇓foldrM* (⇓foldrA-[] φ) = foldrM*-[] φ
⇓foldrA⇒⇓foldrM* (⇓foldrA-∷ ⇓foldrA-undefined φ)
 with ⇑transposeF φ
... | ⇓transposeF-undefined φ′ = foldrM*-undefined φ′
⇓foldrA⇒⇓foldrM* (⇓foldrA-∷ (⇓foldrA-thunk φ₁) φ₂)
 with ⇑transposeF φ₂
... | ⇓transposeF-thunk φ₂′ = foldrM*-thunk (⇓foldrA⇒⇓foldrM* φ₁) φ₂′

⇓foldrM* : ∀ {v₁ v₂ c}
         → ⟦ t₃ ⟧ᵉ γ ∋ v₁
         → ⟦foldrM* t₁ , t₂ ⟧ᵉ γ v₁ ∋ (v₂ , c)
         → ⟦ `foldrM t₁ t₂ t₃ ⟧ᵉ γ ∋ (v₂ , c)
⇓foldrM* φ₁ φ₂ = ⇓foldrA φ₁ (⇓foldrM*⇒⇓foldrA φ₂)

⇓foldrM*-weaken : ∀ {as b} {v : ⟦ τ ⟧ᵗ}
                → ⟦foldrM* t₁ , t₂ ⟧ᵉ γ as ∋ b
                → ⟦foldrM* subsume₂ t₁ , weaken t₂ ⟧ᵉ (γ ⸴ v) as ∋ b
⇓foldrM*-weaken (foldrM*-[] φ)        = foldrM*-[] (⇓weaken φ)
⇓foldrM*-weaken (foldrM*-undefined φ) = foldrM*-undefined (⇓subsume₂ φ)
⇓foldrM*-weaken (foldrM*-thunk φ₁ φ₂) = foldrM*-thunk (⇓foldrM*-weaken φ₁) (⇓subsume₂ φ₂)

⇓foldrM : ∀ {u}
        → ⟦foldrM t₁ , t₂ , t₃ ⟧ᵉ γ ∋ u
        → ⟦ `foldrM t₁ t₂ t₃ ⟧ᵉ γ ∋ u
⇓foldrM (⇓foldrM-intro φ₁ φ₂) = ⇓foldrM* φ₁ φ₂

⇑foldrM : ∀ {u}
        → ⟦ `foldrM t₁ t₂ t₃ ⟧ᵉ γ ∋ u
        → ⟦foldrM t₁ , t₂ , t₃ ⟧ᵉ γ ∋ u
⇑foldrM (⇓foldrA φ₁ φ₂) = ⇓foldrM-intro φ₁ (⇓foldrA⇒⇓foldrM* φ₂)

⇑foldrM*-weaken : ∀ {as b} {v : ⟦ τ ⟧ᵗ}
                → ⟦foldrM* subsume₂ t₁ , weaken t₂ ⟧ᵉ (γ ⸴ v) as ∋ b
                → ⟦foldrM* t₁ , t₂ ⟧ᵉ γ as ∋ b
⇑foldrM*-weaken (foldrM*-[] φ)        = foldrM*-[] (⇑weaken φ)
⇑foldrM*-weaken (foldrM*-undefined φ) = foldrM*-undefined (⇑subsume₂ φ)
⇑foldrM*-weaken (foldrM*-thunk φ₁ φ₂) = foldrM*-thunk (⇑foldrM*-weaken φ₁) (⇑subsume₂ φ₂)

-- Evaluate a term lazily

`lazily : Γ ⊢ `M α → Γ ⊢ `M (`T α)
`lazily t = (t `>>= `return (`thunk (` zeroᵛ))) `? `return `undefined

data ⟦lazily_⟧ᵉ : Γ ⊢ `M α → ⟦ Γ ⟧ᶜ → T ⟦ α ⟧ᵗ × ℕ → Type where
  ⇓lazily-thunk     : ∀ {v c}
                    → ⟦ t ⟧ᵉ γ ∋ (v , c)
                    → ⟦lazily t ⟧ᵉ γ ∋ (thunk v , c)
  ⇓lazily-undefined : ⟦lazily t ⟧ᵉ γ ∋ (undefined , 0)

⇓lazily : ∀ {u} → ⟦lazily t ⟧ᵉ γ ∋ u → ⟦ `lazily t ⟧ᵉ γ ∋ u
⇓lazily (⇓lazily-thunk φ) = ⇓?ˡ (⇓[cost+0] (⇓>>= (⇓>>=-intro φ (⇓return (⇓thunk (⇓ zeroᵛ))))))
⇓lazily ⇓lazily-undefined = ⇓?ʳ (⇓return ⇓undefined)

⇑lazily : ∀ {u} → ⟦ `lazily t ⟧ᵉ γ ∋ u → ⟦lazily t ⟧ᵉ γ ∋ u
⇑lazily (⇓?ˡ φ)
 with ⇑>>= φ
... | ⇓>>=-intro φ₁ (⇓return (⇓thunk (⇓ _))) = ⇓lazily-thunk (⇑[cost+0] φ₁)
⇑lazily (⇓?ʳ (⇓return ⇓undefined)) = ⇓lazily-undefined

-- Force a term

`forced : Γ ⊢ `M (`T α) → Γ ⊢ `M α
`forced t = t `>>= `T-case (` zeroᵛ) (`return (` zeroᵛ)) `fail

data ⟦forced_⟧ᵉ : Γ ⊢ `M (`T α) → ⟦ Γ ⟧ᶜ → ⟦ α ⟧ᵗ × ℕ → Type where
  ⇓forced-intro : ∀ {v c} → ⟦ t ⟧ᵉ γ ∋ (thunk v , c) → ⟦forced t ⟧ᵉ γ ∋ (v , c)

⇓forced : ∀ {u} → ⟦forced t ⟧ᵉ γ ∋ u → ⟦ `forced t ⟧ᵉ γ ∋ u
⇓forced (⇓forced-intro φ) =
  ⇓[cost+0] (⇓>>= (⇓>>=-intro φ (⇓T-case-thunk (⇓ zeroᵛ) (⇓return (⇓ zeroᵛ)))))

⇑forced : ∀ {u} → ⟦ `forced t ⟧ᵉ γ ∋ u → ⟦forced t ⟧ᵉ γ ∋ u
⇑forced φ with ⇑>>= φ
... | ⇓>>=-intro φ₁ (⇓T-case-thunk (⇓ _) (⇓return (⇓ _))) = ⇓forced-intro (⇑[cost+0] φ₁)
