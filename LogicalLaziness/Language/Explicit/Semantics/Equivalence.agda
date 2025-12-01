module LogicalLaziness.Language.Explicit.Semantics.Equivalence where

open import Data.Bool
open import Data.Product
open import Data.Nat
  as ℕ
open import Data.List
open import Data.List.Relation.Unary.All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Data.ListA
open import LogicalLaziness.Base.Data.T
  hiding (All)
open import LogicalLaziness.Language.Explicit
import LogicalLaziness.Language.Explicit.Semantics.Eval
  as 𝔼
open import LogicalLaziness.Language.Explicit.Semantics.Demand
  using ( false
        ; true
        ; []
        ; _∷_
        ; undefined
        ; thunk
        ; _≤ᵉ_
        ; _⊔ᵉ_
        ; _≤ᶜ_
        ; _≤ᵐ_
        ; ⊥ᵐ-minimum
        )
import LogicalLaziness.Language.Explicit.Semantics.Demand
  as 𝔻
open import LogicalLaziness.Language.Explicit.Semantics.Clairvoyant
  using ( false
        ; true
        ; []
        ; _∷_
        ; undefined
        ; thunk
        ; `false
        ; `true
        ; `[]
        ; _`∷_
        ; `tick
        ; `lazy-undefined
        ; `lazy-thunk
        ; `force
        ; _≲ᵉ_
        ; ≲ᵉ-refl
        )
import LogicalLaziness.Language.Explicit.Semantics.Clairvoyant
  as ℂ

mapToList : {A : Type} {P R : A → Type} {Q : Σ A P → Type}
            {xs : List A}
            {pxs : All P xs}
          → (∀ x px → Q (x , px) → R x)
          → All Q (toList pxs)
          → All R xs
mapToList {pxs = []} η [] = []
mapToList {pxs = px ∷ pxs} η (px₁ ∷ qpxs) = η _ px px₁ ∷ mapToList η qpxs

𝔻→𝕃⟦_⟧⌊_⌋ᵉ : (α : Ty) {v : 𝔼.⟦ α ⟧ᵗ} → 𝔻.⟦ α ⟧≺ᵉ v → ℂ.⟦ α ⟧ᵗ
𝔻→𝕃⟦ `Bool   ⟧⌊ false     ⌋ᵉ = false
𝔻→𝕃⟦ `Bool   ⟧⌊ true      ⌋ᵉ = true
𝔻→𝕃⟦ `List α ⟧⌊ []        ⌋ᵉ = []
𝔻→𝕃⟦ `List α ⟧⌊ d ∷ ds    ⌋ᵉ = 𝔻→𝕃⟦ α ⟧⌊ d ⌋ᵉ ∷ 𝔻→𝕃⟦ `T (`List α) ⟧⌊ ds ⌋ᵉ
𝔻→𝕃⟦ `T α    ⟧⌊ undefined ⌋ᵉ = undefined
𝔻→𝕃⟦ `T α    ⟧⌊ thunk d   ⌋ᵉ = thunk 𝔻→𝕃⟦ α ⟧⌊ d ⌋ᵉ

𝔻→𝕃⌊_⌋ᵉ : {α : Ty} {v : 𝔼.⟦ α ⟧ᵗ} → 𝔻.⟦ α ⟧≺ᵉ v → ℂ.⟦ α ⟧ᵗ
𝔻→𝕃⌊ d ⌋ᵉ = 𝔻→𝕃⟦ _ ⟧⌊ d ⌋ᵉ

≤⇒≲ : ∀ {α v} {d₁ d₂ : 𝔻.⟦ α ⟧≺ᵉ v} → d₁ ≤ᵉ d₂ → 𝔻→𝕃⌊ d₁ ⌋ᵉ ≲ᵉ 𝔻→𝕃⌊ d₂ ⌋ᵉ
≤⇒≲ false               = false
≤⇒≲ true                = true
≤⇒≲ undefined           = undefined
≤⇒≲ (thunk d₁₁≤d₂₁)     = thunk (≤⇒≲ d₁₁≤d₂₁)
≤⇒≲ []                  = []
≤⇒≲ (d₁₁≤d₂₁ ∷ d₁₂≤d₂₂) = ≤⇒≲ d₁₁≤d₂₁ ∷ ≤⇒≲ d₁₂≤d₂₂

-- ⊔-≲-l : {α : Ty} {v : 𝔼.⟦ α ⟧ᵗ} (d₁ d₂ : 𝔻.⟦ α ⟧≺ᵉ v) → ⌊ d₁ ⌋ᵉ ≲ᵉ ⌊ d₁ ⊔ᵉ d₂ ⌋ᵉ
-- ⊔-≲-l false false             = false
-- ⊔-≲-l true true               = true
-- ⊔-≲-l undefined d₂            = undefined
-- ⊔-≲-l (thunk d₁₁) undefined   = ≲ᵉ-refl
-- ⊔-≲-l (thunk d₁₁) (thunk d₂₁) = thunk (⊔-≲-l d₁₁ d₂₁)
-- ⊔-≲-l [] []                   = []
-- ⊔-≲-l (d₁₁ ∷ d₁₂) (d₂₁ ∷ d₂₂) = ⊔-≲-l d₁₁ d₂₁ ∷ ⊔-≲-l d₁₂ d₂₂

𝔻→𝕃⟦_⟧⌊_⌋ᶜ : (Γ : Ctx) {γ : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ γ → ℂ.⟦ Γ ⟧ᶜ
𝔻→𝕃⟦ Γ ⟧⌊ δ ⌋ᶜ = mapToList (λ α _ d → 𝔻→𝕃⟦ α ⟧⌊ d ⌋ᵉ) δ

𝔻→𝕃⌊_⌋ᶜ : {Γ : Ctx} {γ : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ γ → ℂ.⟦ Γ ⟧ᶜ
𝔻→𝕃⌊ δ ⌋ᶜ = 𝔻→𝕃⟦ _ ⟧⌊ δ ⌋ᶜ

-- functional-correctness : {Γ : Ctx} {γ : 𝔼.⟦ Γ ⟧ᶜ} {χ : ℂ.⟦ Γ ⟧ᶜ}
--                          (t : Γ ⊢ α)
--                        → χ ≺ᶜ γ
--                        → ℂ.⟦ t ⟧ χ ∋ a
--                        → a ≺ᶜ 𝔼.⟦ t ⟧ γ

postulate
  cost-existence :
    ∀ {Γ α} (M : Γ ⊢ α)
      (g : 𝔼.⟦ Γ ⟧ᶜ) (a₁ : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ M ⟧ᵉ g)
    → let (g₁ , n) = 𝔻.⟦ M ⟧ᵉ g a₁
      in (g₂ : 𝔻.⟦ Γ ⟧≺ᶜ g)
       → g₁ ≤ᶜ g₂
       → Σ[ a₂ ∈ 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ M ⟧ᵉ g ] (a₁ ≤ᵉ a₂ × ℂ.⟦ M ⟧ᵉ 𝔻→𝕃⌊ g₂ ⌋ᶜ ∋ (𝔻→𝕃⌊ a₂ ⌋ᵉ , n))

  cost-minimality :
    ∀ {Γ α}
      {t : Γ ⊢ α}
      (γ : 𝔼.⟦ Γ ⟧ᶜ)
      (a₁ : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ)
      {δ₂ : 𝔻.⟦ Γ ⟧≺ᶜ γ}
      {a₂ : ℂ.⟦ α ⟧ᵗ}
      {c₂ : ℕ}
    → ℂ.⟦ t ⟧ᵉ 𝔻→𝕃⌊ δ₂ ⌋ᶜ ∋ (a₂ , c₂)
    → let (δ₁ , c₁) = 𝔻.⟦ t ⟧ᵉ γ a₁
      in (δ₁ , c₁) ≤ᵐ (δ₂ , c₂)
-- cost-minimality γ a₁ (ℂ.` x) = {!!} , z≤n
-- cost-minimality γ a₁ (ℂ.`let x `in x₁) = {!!}
-- cost-minimality γ a₁ `false = ⊥ᵐ-minimum _
-- cost-minimality γ a₁ `true = ⊥ᵐ-minimum _
-- cost-minimality {t = t₁} γ a₁ (ℂ.`if φ `else φ₁) = {!!}
-- cost-minimality γ a₁ (ℂ.`if φ `then φ₁) = {!!}
-- cost-minimality γ a₁ `[] = ⊥ᵐ-minimum _
-- cost-minimality γ a₁ (x `∷ x₁) = {!!}
-- cost-minimality γ a₁ (ℂ.`foldr x x₁) = {!!}
-- cost-minimality γ a₁ (`tick x) = cost-minimality γ a₁ x .proj₁ , s≤s (cost-minimality γ a₁ x .proj₂)
-- cost-minimality γ (thunk a₁) `lazy-undefined = {!`lazy-undefined!}
-- cost-minimality γ undefined `lazy-undefined = ⊥ᵐ-minimum _
-- cost-minimality γ (thunk a₁) (`lazy-thunk x) = cost-minimality γ a₁ x
-- cost-minimality γ undefined (`lazy-thunk x) = ⊥ᵐ-minimum _
-- cost-minimality γ a₁ (`force x) = cost-minimality γ (thunk a₁) x
-- -- ℂ.⟦ t ⟧ᵉ ⌊ inDs ⌋ᶜ ∋ (⌊ outD ⌋ᵉ , c)
-- -- theorem₁ (` x) γ outD = {!!}
-- -- theorem₁ (`let t₁ `in t₂) γ outD = {!!}
-- -- theorem₁ `false γ false = `false
-- -- theorem₁ `true γ true = `true
-- -- theorem₁ (`if t₁ `then t₂ `else t₃) γ outD = {!!}
-- -- theorem₁ `[] γ [] = `[]
-- -- theorem₁ (t₁ `∷ t₂) γ (outD₁ ∷ outD₂) = {!theorem₁ t₁ γ outD₁!}
-- -- theorem₁ (`foldr t t₁ t₂) γ outD = {!!}
-- -- theorem₁ (`tick t) γ outD = `tick (theorem₁ t γ outD)
-- -- theorem₁ (`lazy t) γ undefined = `lazy-undefined
-- -- theorem₁ (`lazy t) γ (thunk outD) = `lazy-thunk (theorem₁ t γ outD)
-- -- theorem₁ (`force t) γ outD = `force (theorem₁ t γ (thunk outD))



-- theorem₁′ :
--   ∀ {Γ α}
--     (M : Γ ⊢ α)
--     (g : 𝔼.⟦ Γ ⟧ᶜ)
--     (outD : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ M ⟧ᵉ g) →
--     let (inDs , c) = 𝔻.⟦ M ⟧ᵉ g outD
--     in ℂ.⟦ M ⟧ᵉ ⌊ inDs ⌋ᶜ ∋ (⌊ outD ⌋ᵉ , c)
-- theorem₁′ = {!!}



-- theorem₁ (` x) γ outD = {!!}
-- theorem₁ (`let t₁ `in t₂) γ outD = {!!}
-- theorem₁ `false γ false = `false
-- theorem₁ `true γ true = `true
-- theorem₁ (`if t₁ `then t₂ `else t₃) γ outD = {!!}
-- theorem₁ `[] γ [] = `[]
-- theorem₁ (t₁ `∷ t₂) γ (outD₁ ∷ outD₂) = {!theorem₁ t₁ γ outD₁!}
-- theorem₁ (`foldr t t₁ t₂) γ outD = {!!}
-- theorem₁ (`tick t) γ outD = `tick (theorem₁ t γ outD)
-- theorem₁ (`lazy t) γ undefined = `lazy-undefined
-- theorem₁ (`lazy t) γ (thunk outD) = `lazy-thunk (theorem₁ t γ outD)
-- theorem₁ (`force t) γ outD = `force (theorem₁ t γ (thunk outD))
