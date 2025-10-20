module LogicalLaziness.Language.Explicit.Semantics.Clairvoyant where

open import Relation.Binary
open import Data.Bool
  hiding (T)
open import Data.Product
open import Data.Nat
open import Data.List.Relation.Unary.All
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Data.List.All.Relation.Binary.Pointwise
  renaming (Pointwise to AllPointwise)
open import LogicalLaziness.Base.Data.T
  hiding (All)
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Base.Data.ListA
  as ListA
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
    x : α ∈ᴸ Γ
    γ γ₁ γ₂ : ⟦ Γ ⟧ᶜ

mutual

  data ⟦_⟧ᵉ : Γ ⊢ τ → ⟦ Γ ⟧ᶜ → ⟦ τ ⟧ᵗ × ℕ → Type where
    `_ :
        (x : α ∈ᴸ Γ)
      → ⟦ ` x ⟧ᵉ γ ∋ (All.lookup γ x , 0)
    `let_`in_ :
      ∀ {t₁ : Γ ⊢ α} {t₂ : Γ ⸴ α ⊢ β} {a b c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a , c₁)
      → ⟦ t₂ ⟧ᵉ (γ ⸴ a) ∋ (b , c₂)
      → ⟦ `let t₁ `in t₂ ⟧ᵉ γ ∋ (b , c₁ + c₂)
    `false : ⟦ `false ⟧ᵉ γ ∋ (false , 0)
    `true : ⟦ `true ⟧ᵉ γ ∋ (true , 0)
    `if_`else_ :
      ∀ {t₁} {t₂ t₃ : Γ ⊢ τ} {v c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ (false , c₁)
      → ⟦ t₃ ⟧ᵉ γ (v , c₂)
      → ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ (v , c₁ + c₂)
    `if_`then_ :
      ∀ {t₁} {t₂ t₃ : Γ ⊢ τ} {v c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ (true , c₁)
      → ⟦ t₂ ⟧ᵉ γ (v , c₂)
      → ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ (v , c₁ + c₂)
    `[] : ⟦ `[] ∶ Γ ⊢ `List τ ⟧ᵉ γ ∋ ([] , 0)
    _`∷_ :
      ∀ {t₁ : Γ ⊢ `T τ} {t₂ : Γ ⊢ `T (`List τ)} {a₁ a₂ c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a₁ , c₁)
      → ⟦ t₂ ⟧ᵉ γ ∋ (a₂ , c₂)
      → ⟦ t₁ `∷ t₂ ⟧ᵉ γ ∋ (a₁ ∷ a₂ , c₁ + c₂)
    `foldr :
      ∀ {t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β} {t₂ : Γ ⊢ β} {t₃ : Γ ⊢ `List α}
        {as b c₁ c₂}
      → ⟦foldr t₁ , t₂ ⟧ᵉ γ as ∋ (b , c₂)
      → ⟦ t₃ ⟧ᵉ γ ∋ (as , c₁)
      → ⟦ `foldr t₁ t₂ t₃ ⟧ᵉ γ ∋ (b , c₁ + c₂)
    `tick :
      ∀ {t₁ : Γ ⊢ τ} {a c}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a , c)
      → ⟦ `tick t₁ ⟧ᵉ γ ∋ (a , suc c)
    `lazy-undefined :
      ∀ {t₁ : Γ ⊢ τ}
      → ⟦ `lazy t₁ ⟧ᵉ γ ∋ (undefined , 0)
    `lazy-thunk :
      ∀ {t₁ : Γ ⊢ τ} {a c}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a , c)
      → ⟦ `lazy t₁ ⟧ᵉ γ ∋ (thunk a , c)
    `force :
      ∀ {t₁ : Γ ⊢ `T τ} {a c}
      → ⟦ t₁ ⟧ᵉ γ ∋ (thunk a , c)
      → ⟦ `force t₁ ⟧ᵉ γ ∋ (a , c)

  data ⟦foldr_,_⟧ᵉ (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) (t₂ : Γ ⊢ β) : ⟦ Γ ⟧ᶜ → ListA ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ × ℕ → Type where
    `foldr-[] :
      ∀ {g b c}
      → ⟦ t₂ ⟧ᵉ g ∋ (b , c)
      → ⟦foldr t₁ , t₂ ⟧ᵉ g [] ∋ (b , c)
    `foldr-∷ :
      ∀ {g a as b b′ c₁ c₂}
      → ⟦foldr′ t₁ , t₂ ⟧ᵉ g as ∋ (b , c₂)
      → ⟦ t₁ ⟧ᵉ (g ⸴ a ⸴ b) ∋ (b′ , c₁)
      → ⟦foldr t₁ , t₂ ⟧ᵉ g (a ∷ as) ∋ (b′ , c₁ + c₂)

  data ⟦foldr′_,_⟧ᵉ (t₁ : Γ ⸴ `T α ⸴ `T β ⊢ β) (t₂ : Γ ⊢ β) : ⟦ Γ ⟧ᶜ → T (ListA ⟦ α ⟧ᵗ) → T ⟦ β ⟧ᵗ × ℕ → Type where
    `foldr′-undefined :
      ∀ {g}
      → ⟦foldr′ t₁ , t₂ ⟧ᵉ g undefined ∋ (undefined , 0)
    `foldr′-thunk :
      ∀ {g as b c}
      → ⟦foldr t₁ , t₂ ⟧ᵉ g as ∋ (b , c)
      → ⟦foldr′ t₁ , t₂ ⟧ᵉ g (thunk as) ∋ (thunk b , c)

data ⟦_⟧[_≲ᵉ_] : (α : Ty) → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type where
  undefined : ∀ {v}
            → ⟦ `T α         ⟧[ undefined ≲ᵉ v         ]
  thunk     : ∀ {v v′}
            → ⟦ α            ⟧[ v         ≲ᵉ v′        ]
            → ⟦ `T α         ⟧[ thunk v   ≲ᵉ thunk v′  ]
  false     : ⟦ `Bool        ⟧[ false     ≲ᵉ false     ]
  true      : ⟦ `Bool        ⟧[ true      ≲ᵉ true      ]
  []        : ⟦ `List α      ⟧[ []        ≲ᵉ []        ]
  _∷_       : ∀ {v₁ v₁′ v₂ v₂′}
            → ⟦ `T α         ⟧[ v₁        ≲ᵉ v₁′       ]
            → ⟦ `T (`List α) ⟧[ v₂        ≲ᵉ v₂′       ]
            → ⟦ `List α      ⟧[ v₁ ∷ v₂   ≲ᵉ v₁′ ∷ v₂′ ]

_≲ᵉ_ : {α : Ty} → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type
v₁ ≲ᵉ v₂ = ⟦ _ ⟧[ v₁ ≲ᵉ v₂ ]

≲ᵉ-refl : Reflexive ⟦ α ⟧[_≲ᵉ_]
≲ᵉ-refl {α = `Bool} {x = false} = false
≲ᵉ-refl {α = `Bool} {x = true} = true
≲ᵉ-refl {α = `T α} {x = undefined} = undefined
≲ᵉ-refl {α = `T α} {x = thunk x} = thunk ≲ᵉ-refl
≲ᵉ-refl {α = `List α} = ListA.ind (λ x → ⟦ `List α ⟧[ x ≲ᵉ x ]) [] (λ{ undefined _ undefined → undefined ∷ undefined ; undefined _ (thunk x) → undefined ∷ thunk x ; (thunk x) _ undefined → thunk ≲ᵉ-refl ∷ undefined ; (thunk x) _ (thunk x₁) → thunk ≲ᵉ-refl ∷ thunk x₁ }) _

⟦_⟧[_≲_]ᶜ : (Γ : Ctx) → ⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ → Type
⟦ Γ ⟧[ γ₁ ≲ γ₂ ]ᶜ = AllPointwise ⟦ _ ⟧[_≲ᵉ_] γ₁ γ₂

-- ≲-refl : Reflexive ⟦ Γ ⟧[_≲_]ᶜ
-- ≲-refl = {!!}

-- ctx-mono-var : (x : α ∈ᴸ Γ)
--              → ⟦ Γ ⟧[ γ₁ ≲ γ₂ ]ᶜ
--              → ⟦ ` x ⟧ᵉ γ₂ ∋

-- ctx-mono : {t : Γ ⊢ α} {v : ⟦ α ⟧ᵗ} {c : ℕ} → ⟦ Γ ⟧[ γ₁ ≲ γ₂ ]ᶜ → ⟦ t ⟧ᵉ γ₁ ∋ (v , c) → ⟦ t ⟧ᵉ γ₂ ∋ (v , c)
-- ctx-mono γ₁≲γ₂ (` x) = {!` ?!}
-- ctx-mono γ₁≲γ₂ (`let φ₁ `in φ₂) = `let ctx-mono γ₁≲γ₂ φ₁ `in ctx-mono (γ₁≲γ₂ ⸴ ≲ᵉ-refl) φ₂
-- ctx-mono γ₁≲γ₂ `false = `false
-- ctx-mono γ₁≲γ₂ `true = `true
-- ctx-mono γ₁≲γ₂ (`if φ₁ `else φ₂) = `if ctx-mono γ₁≲γ₂ φ₁ `else ctx-mono γ₁≲γ₂ φ₂
-- ctx-mono γ₁≲γ₂ (`if φ₁ `then φ₂) = `if ctx-mono γ₁≲γ₂ φ₁ `then ctx-mono γ₁≲γ₂ φ₂
-- ctx-mono γ₁≲γ₂ `[] = `[]
-- ctx-mono γ₁≲γ₂ (φ₁ `∷ φ₂) = ctx-mono γ₁≲γ₂ φ₁ `∷ ctx-mono γ₁≲γ₂ φ₂
-- ctx-mono γ₁≲γ₂ (`foldr φ₁ φ₂) = {!!}
-- ctx-mono γ₁≲γ₂ (`tick φ) = `tick (ctx-mono γ₁≲γ₂ φ)
-- ctx-mono γ₁≲γ₂ `lazy-undefined = `lazy-undefined
-- ctx-mono γ₁≲γ₂ (`lazy-thunk φ) = `lazy-thunk (ctx-mono γ₁≲γ₂ φ)
-- ctx-mono γ₁≲γ₂ (`force φ) = `force (ctx-mono γ₁≲γ₂ φ)
