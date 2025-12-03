module LogicalLaziness.Language.Explicit.Semantics.Clairvoyant where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Bool
  hiding (T)
open import Data.Product
open import Data.Nat
open import Data.List.Relation.Unary.All
  as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Effect.Monad.Tick
import LogicalLaziness.Base.Data.List.All
  as All
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
open import LogicalLaziness.Language.Explicit.Semantics.Demand
  as 𝔻
  using ( false
        ; true
        ; undefined
        ; thunk
        ; []
        ; _∷_
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
    t : Γ ⊢ α
    γ γ₁ γ₂ : ⟦ Γ ⟧ᶜ
    c₁ c₂ : ℕ

-- Convert from demand semantics values

𝔻⟦_⟧[_]ᵗ : (α : Ty) {v : 𝔼.⟦ α ⟧ᵗ} → 𝔻.⟦ α ⟧≺ᵗ v → ⟦ α ⟧ᵗ
𝔻⟦ `Bool   ⟧[ false     ]ᵗ = false
𝔻⟦ `Bool   ⟧[ true      ]ᵗ = true
𝔻⟦ `T α    ⟧[ undefined ]ᵗ = undefined
𝔻⟦ `T α    ⟧[ thunk v   ]ᵗ = thunk 𝔻⟦ α ⟧[ v ]ᵗ
𝔻⟦ `List α ⟧[ []        ]ᵗ = []
𝔻⟦ `List α ⟧[ v ∷ vs    ]ᵗ = 𝔻⟦ α ⟧[ v ]ᵗ ∷ 𝔻⟦ `T (`List α) ⟧[ vs ]ᵗ

𝔻[_]ᵗ : {v : 𝔼.⟦ α ⟧ᵗ} → 𝔻.⟦ α ⟧≺ᵗ v → ⟦ α ⟧ᵗ
𝔻[_]ᵗ = 𝔻⟦ _ ⟧[_]ᵗ

𝔻⟦_⟧[_]ᶜ : (Γ : Ctx) {γ : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ γ → ⟦ Γ ⟧ᶜ
𝔻⟦ _ ⟧[ γ ]ᶜ = All.uncurry-const⁻ (All.map 𝔻[_]ᵗ γ)

𝔻[_]ᶜ : {γ : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ γ → ⟦ Γ ⟧ᶜ
𝔻[_]ᶜ = 𝔻⟦ _ ⟧[_]ᶜ

-- Convert from evaluation semantics values
--
-- It may seem unnecessarily complicated to pass through the conversion to
-- demand semantics, but it gives us some useful judgmental equalities later on.

𝔼⟦_⟧[_]ᵗ : (α : Ty) → 𝔼.⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ
𝔼⟦ α ⟧[ v ]ᵗ = 𝔻⟦ α ⟧[ 𝔻.𝔼⟦ α ⟧[ v ]ᵗ ]ᵗ

𝔼[_]ᵗ : 𝔼.⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ
𝔼[_]ᵗ = 𝔼⟦ _ ⟧[_]ᵗ

𝔼⟦_⟧[_]ᶜ : (Γ : Ctx) → 𝔼.⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ
𝔼⟦ Γ ⟧[ γ ]ᶜ = 𝔻⟦ Γ ⟧[ 𝔻.𝔼⟦ Γ ⟧[ γ ]ᶜ ]ᶜ

𝔼[_]ᶜ : 𝔼.⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ
𝔼[_]ᶜ = 𝔼⟦ _ ⟧[_]ᶜ

-- Semantics

mutual

  data ⟦_⟧ᵉ : Γ ⊢ α → ⟦ Γ ⟧ᶜ → Tick ⟦ α ⟧ᵗ → Type where
    ⇓_ :
        (x : α ∈ᴸ Γ)
      → ⟦ ` x ⟧ᵉ γ ∋ (All.lookup γ x , 0)
    ⇓let_⇓in_ :
      ∀ {t₁ : Γ ⊢ α} {t₂ : Γ ⸴ α ⊢ β} {a b c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a , c₁)
      → ⟦ t₂ ⟧ᵉ (γ ⸴ a) ∋ (b , c₂)
      → ⟦ `let t₁ `in t₂ ⟧ᵉ γ ∋ (b , c₁ + c₂)
    ⇓false : ⟦ `false ⟧ᵉ γ ∋ (false , 0)
    ⇓true : ⟦ `true ⟧ᵉ γ ∋ (true , 0)
    ⇓if_⇓else_ :
      ∀ {t₁} {t₂ t₃ : Γ ⊢ α} {v c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ (false , c₁)
      → ⟦ t₃ ⟧ᵉ γ (v , c₂)
      → ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ (v , c₁ + c₂)
    ⇓if_⇓then_ :
      ∀ {t₁} {t₂ t₃ : Γ ⊢ α} {v c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ (true , c₁)
      → ⟦ t₂ ⟧ᵉ γ (v , c₂)
      → ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ γ (v , c₁ + c₂)
    ⇓[] : ⟦ `[] ∶ Γ ⊢ `List τ ⟧ᵉ γ ∋ ([] , 0)
    _⇓∷_ :
      ∀ {t₁ : Γ ⊢ α} {t₂ : Γ ⊢ `T (`List α)} {a₁ a₂ c₁ c₂}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a₁ , c₁)
      → ⟦ t₂ ⟧ᵉ γ ∋ (a₂ , c₂)
      → ⟦ t₁ `∷ t₂ ⟧ᵉ γ ∋ (a₁ ∷ a₂ , c₁ + c₂)
    ⇓foldr :
      ∀ {t₁ : Γ ⸴ α ⸴ `T β ⊢ β} {t₂ : Γ ⊢ β} {t₃ : Γ ⊢ `List α}
        {as b c₁ c₂}
      → ⟦ t₃ ⟧ᵉ γ ∋ (as , c₁)
      → ⟦foldr t₁ , t₂ ⟧ᵉ γ as ∋ (b , c₂)
      → ⟦ `foldr t₁ t₂ t₃ ⟧ᵉ γ ∋ (b , c₁ + c₂)
    ⇓tick :
      ∀ {t₁ : Γ ⊢ α} {a c}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a , c)
      → ⟦ `tick t₁ ⟧ᵉ γ ∋ (a , suc c)
    ⇓lazy-undefined :
      ∀ {t₁ : Γ ⊢ α}
      → ⟦ `lazy t₁ ⟧ᵉ γ ∋ (undefined , 0)
    ⇓lazy-thunk :
      ∀ {t₁ : Γ ⊢ α} {a c}
      → ⟦ t₁ ⟧ᵉ γ ∋ (a , c)
      → ⟦ `lazy t₁ ⟧ᵉ γ ∋ (thunk a , c)
    ⇓force :
      ∀ {t₁ : Γ ⊢ `T α} {a c}
      → ⟦ t₁ ⟧ᵉ γ ∋ (thunk a , c)
      → ⟦ `force t₁ ⟧ᵉ γ ∋ (a , c)
 
  data ⟦foldr_,_⟧ᵉ (t₁ : Γ ⸴ α ⸴ `T β ⊢ β) (t₂ : Γ ⊢ β) : ⟦ Γ ⟧ᶜ → ListA ⟦ α ⟧ᵗ → Tick ⟦ β ⟧ᵗ → Type where
    ⇓foldr-[] :
      ∀ {γ b c}
      → ⟦ t₂ ⟧ᵉ γ ∋ (b , c)
      → ⟦foldr t₁ , t₂ ⟧ᵉ γ [] ∋ (b , c)
    ⇓foldr-∷ : ∀ {a asT b₁ b₂ c₁ c₂}
              → ⟦foldr′ t₁ , t₂ ⟧ᵉ γ asT ∋ (b₁ , c₁)
              → ⟦ t₁ ⟧ᵉ (γ ⸴ a ⸴ b₁) ∋ (b₂ , c₂)
              → ⟦foldr t₁ , t₂ ⟧ᵉ γ (a ∷ asT) ∋ (b₂ , c₁ + c₂)

  data ⟦foldr′_,_⟧ᵉ (t₁ : Γ ⸴ α ⸴ `T β ⊢ β)
                    (t₂ : Γ ⊢ β) :
                    ⟦ Γ ⟧ᶜ → T (ListA ⟦ α ⟧ᵗ) → Tick (T ⟦ β ⟧ᵗ) → Type where
    ⇓foldr′-undefined : ⟦foldr′ t₁ , t₂ ⟧ᵉ γ undefined ∋ pure undefined
    ⇓foldr′-thunk     : ∀ {as b c}
                      → ⟦foldr t₁ , t₂ ⟧ᵉ γ as ∋ (b , c)
                      → ⟦foldr′ t₁ , t₂ ⟧ᵉ γ (thunk as) ∋ (thunk b , c)

⇓cost≡ : ∀ {v} → c₁ ≡ c₂ → ⟦ t ⟧ᵉ γ ∋ (v , c₁) → ⟦ t ⟧ᵉ γ ∋ (v , c₂)
⇓cost≡ refl φ = φ

data ⟦_⟧[_≤ᵗ_] : (α : Ty) → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type where
  undefined : ∀ {v}
            → ⟦ `T α         ⟧[ undefined ≤ᵗ v         ]
  thunk     : ∀ {v v′}
            → ⟦ α            ⟧[ v         ≤ᵗ v′        ]
            → ⟦ `T α         ⟧[ thunk v   ≤ᵗ thunk v′  ]
  false     : ⟦ `Bool        ⟧[ false     ≤ᵗ false     ]
  true      : ⟦ `Bool        ⟧[ true      ≤ᵗ true      ]
  []        : ⟦ `List α      ⟧[ []        ≤ᵗ []        ]
  _∷_       : ∀ {v₁ v₁′ v₂ v₂′}
            → ⟦ α            ⟧[ v₁        ≤ᵗ v₁′       ]
            → ⟦ `T (`List α) ⟧[ v₂        ≤ᵗ v₂′       ]
            → ⟦ `List α      ⟧[ v₁ ∷ v₂   ≤ᵗ v₁′ ∷ v₂′ ]

infix 4 _≤ᵗ_
_≤ᵗ_ : {α : Ty} → ⟦ α ⟧ᵗ → ⟦ α ⟧ᵗ → Type
v₁ ≤ᵗ v₂ = ⟦ _ ⟧[ v₁ ≤ᵗ v₂ ]

⟦_⟧[_≤ᶜ_] : (Γ : Ctx) → ⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ → Type
⟦ Γ ⟧[ γ₁ ≤ᶜ γ₂ ] = AllPointwise ⟦ _ ⟧[_≤ᵗ_] γ₁ γ₂

infix 4 _≤ᶜ_
_≤ᶜ_ : {Γ : Ctx} → ⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ → Type
_≤ᶜ_ = ⟦ _ ⟧[_≤ᶜ_]

𝔻≤⇒≤ᵗ : ∀ {v} {d₁ d₂ : 𝔻.⟦ α ⟧≺ᵗ v} → d₁ 𝔻.≤ᵗ d₂ → 𝔻[ d₁ ]ᵗ ≤ᵗ 𝔻[ d₂ ]ᵗ
𝔻≤⇒≤ᵗ false     = false
𝔻≤⇒≤ᵗ true      = true
𝔻≤⇒≤ᵗ undefined = undefined
𝔻≤⇒≤ᵗ (thunk φ) = thunk (𝔻≤⇒≤ᵗ φ)
𝔻≤⇒≤ᵗ []        = []
𝔻≤⇒≤ᵗ (φ ∷ Φ)   = 𝔻≤⇒≤ᵗ φ ∷ 𝔻≤⇒≤ᵗ Φ

𝔻≤⇒≤ᶜ : ∀ {γ} {γ₁ γ₂ : 𝔻.⟦ Γ ⟧≺ᶜ γ} → γ₁ 𝔻.≤ᶜ γ₂ → 𝔻[ γ₁ ]ᶜ ≤ᶜ 𝔻[ γ₂ ]ᶜ
𝔻≤⇒≤ᶜ {Γ = ∅    } {∅    } {∅    } {∅    } φ       = ∅
𝔻≤⇒≤ᶜ {Γ = _ ⸴ _} {_ ⸴ _} {_ ⸴ _} {_ ⸴ _} (Φ ⸴ φ) = 𝔻≤⇒≤ᶜ Φ ⸴ 𝔻≤⇒≤ᵗ φ

𝔻≤𝔼ᵗ : ∀ {v} (d : 𝔻.⟦ α ⟧≺ᵗ v) → 𝔻[ d ]ᵗ ≤ᵗ 𝔼[ v ]ᵗ
𝔻≤𝔼ᵗ false     = false
𝔻≤𝔼ᵗ true      = true
𝔻≤𝔼ᵗ (thunk d) = thunk (𝔻≤𝔼ᵗ d)
𝔻≤𝔼ᵗ undefined = undefined
𝔻≤𝔼ᵗ []        = []
𝔻≤𝔼ᵗ (d ∷ ds)  = 𝔻≤𝔼ᵗ d ∷ 𝔻≤𝔼ᵗ ds

𝔻≤𝔼ᶜ : ∀ {γ} (γᴬ : 𝔻.⟦ Γ ⟧≺ᶜ γ) → 𝔻[ γᴬ ]ᶜ ≤ᶜ 𝔼[ γ ]ᶜ
𝔻≤𝔼ᶜ {Γ = ∅     } {∅    } ∅          = ∅
𝔻≤𝔼ᶜ {Γ = _ ⸴ _ } {_ ⸴ _} (γsᴬ ⸴ γᴬ) = 𝔻≤𝔼ᶜ γsᴬ ⸴ 𝔻≤𝔼ᵗ γᴬ
