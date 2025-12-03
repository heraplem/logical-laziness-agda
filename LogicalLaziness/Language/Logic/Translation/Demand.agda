module LogicalLaziness.Language.Logic.Translation.Demand where

open import Relation.Binary.PropositionalEquality
  hiding ([_])
open import Data.Bool
  using ( false
        ; true
        )
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.List.Properties
  as List
import Data.List.Relation.Unary.All
  as List
import Data.List.Relation.Unary.All.Properties
  as All
open import Data.List.Membership.Propositional.Properties

open import LogicalLaziness.Base
open import LogicalLaziness.Base.Effect.Monad.Tick
import LogicalLaziness.Base.Data.List
  as List
import LogicalLaziness.Base.Data.List.All
  as All
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Base.Data.T
open import LogicalLaziness.Base.Data.ListA
import LogicalLaziness.Language.Explicit
  as Explicit
import LogicalLaziness.Language.Explicit.Semantics.Eval
  as 𝔼
import LogicalLaziness.Language.Explicit.Semantics.Clairvoyant
  as ℂ
import LogicalLaziness.Language.Explicit.Semantics.Demand
  as 𝔻
open import LogicalLaziness.Language.Explicit.Semantics.Equivalence
  as 𝐁
open import LogicalLaziness.Language.Logic.Base
open import LogicalLaziness.Language.Logic.Renaming
open import LogicalLaziness.Language.Logic.Construct
import LogicalLaziness.Language.Logic.Translation.Base
  as 𝕃
import LogicalLaziness.Language.Logic.Translation.Eval
  as 𝔼
import LogicalLaziness.Language.Logic.Translation.Clairvoyance
  as ℂ
import LogicalLaziness.Language.Logic.Equivalence.Clairvoyance
  as ℂ

⌊_⌋ᵗ : ∀ {α} {v : 𝔼.⟦ α ⟧ᵗ} → 𝔻.⟦ α ⟧≺ᵗ v → 𝕃.⟦⌊ α ⌋⟧ᵗ
⌊ d ⌋ᵗ = ℂ.⌊ ℂ.𝔻[ d ]ᵗ ⌋ᵗ

⌊_⌋ᶜ : ∀ {Γ} {γ : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ γ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⌊_⌋ᶜ {γ = γ} δ = ℂ.⌊ ℂ.𝔻[ δ ]ᶜ ⌋ᶜ

final : Γ ⊢ α `× β
      → Γ ⸴ α ⊢ ∣ Γ ∣ `× β
final t =
  `let (weaken t) `in
  `assert ` sucᵛ zeroᵛ `≟ `proj₁ (` zeroᵛ) `in
  weaken (weaken `ctx) `, `proj₂ (` zeroᵛ)

⇓final : ∀ {v : ⟦ α ⟧ᵗ} {c}
       → ⟦ t ⟧ᵉ γ ∋ (v , c)
       → ⟦ final t ⟧ᵉ (γ ⸴ v) ∋ (∥ γ ∥ , c)
⇓final φ =
  ⇓let ⇓weaken φ ⇓in
  ⇓assert ⇓≟-true (⇓ sucᵛ zeroᵛ) (⇓proj₁ (⇓ zeroᵛ)) ⇓in
  ⇓weaken (⇓weaken ⇓ctx) ⇓, ⇓proj₂ (⇓ zeroᵛ)

sink : Γ …⸴ Δ ⸴ τ ⊢ α → Γ ⸴ τ …⸴ Δ ⊢ α
sink = {!!}

⇓sink : {γ : ⟦ Γ ⟧ᶜ} {δ : ⟦ Δ ⟧ᶜ}
        {v′ : ⟦ τ ⟧ᵗ} {v : ⟦ α ⟧ᵗ}
      → ⟦ t ⟧ᵉ (γ …⸴′ δ ⸴ v′) ∋ v
      → ⟦ sink {Γ = Γ} {Δ = Δ} t ⟧ᵉ (γ ⸴ v′ …⸴′ δ) ∋ v
⇓sink = {!!}

wrap : Γ ⊢ α `× β
     → Γ ⸴ α ⊢ ∣ Γ ∣ `× β
wrap {Γ = Γ} {α = α} t =
  `let-free* Γ `in
  `assert gweakenl {Γ = Γ} `ctx `≲ gweakenr (weaken `ctx)
  `in sink (gweakenl {Δ = Γ} (final t))

-- base language 𝐁
--   evaluation semantics 𝔼
--   clairvoyance semantics ℂ
--   demand semantics 𝔻
-- logic language 𝐋
--   logic semantics 𝕃

⇓wrap : ∀ {γ′ : ⟦ Γ ⟧ᶜ} {v : ⟦ α ⟧ᵗ}
      → ⟦ t ⟧ᵉ γ′ ∋ (v , c)
      → γ′ ≲ᶜ γ
      → ⟦ wrap t ⟧ᵉ (γ ⸴ v) ∋ (∥ γ′ ∥ , c)
⇓wrap {γ = γ} {γ′ = γ′} {v = v} φ ψ =
  ⇓let-free* γ′ ⇓in
  ⇓assert ⇓≲-true (⇓gweakenl (γ ⸴ v) γ′ ⇓ctx) (⇓gweakenr (γ ⸴ v) γ′ (⇓weaken ⇓ctx)) (≲ᶜ⇒≲ᵗ ψ) ⇓in
  ⇓sink (⇓gweakenl γ (γ′ ⸴ v) (⇓final φ))

⌊_⌋ᵉ : ∀ {Γ α}
     → Explicit.Tm Γ α
     →  𝕃.⌊ Γ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
⌊ t ⌋ᵉ = wrap ℂ.⌊ t ⌋ᵉ

⟦⌊_⌋⟧ᵉ : ∀ {Γ α} (t : Explicit.Tm Γ α)
       → 𝕃.⟦⌊ Γ ⸴ α ⌋⟧ᶜ → Tick ⟦ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ ⟧ᵗ → Type
⟦⌊ t ⌋⟧ᵉ = ⟦ ⌊ t ⌋ᵉ ⟧ᵉ

⇓⌊⌋ᵉ : ∀ {Γ α} {t : Explicit.Tm Γ α}
         {γ γᴬ : 𝕃.⟦⌊ Γ ⌋⟧ᶜ} {vᴬ c}
      → γᴬ ≲ᶜ γ
      → ℂ.⟦⌊ t ⌋⟧ᵉ γᴬ ∋ (vᴬ , c)
      → ⟦⌊ t ⌋⟧ᵉ (γ ⸴ vᴬ) ∋ (∥ γᴬ ∥ , c)
⇓⌊⌋ᵉ ψ φ = ⇓wrap φ ψ

ℂ⟦⌊⌋⟧ᵉ : ∀ {Γ α} {t : Explicit.Tm Γ α}
           {γ γᴬ aᴬ c}
        → γᴬ ℂ.≤ᶜ γ
        → ℂ.⟦ t ⟧ᵉ γᴬ ∋ (aᴬ , c)
        → ⟦⌊ t ⌋⟧ᵉ (ℂ.⌊ γ ⌋ᶜ ⸴ ℂ.⌊ aᴬ ⌋ᵗ) ∋ (∥ ℂ.⌊ γᴬ ⌋ᶜ ∥ , c)
ℂ⟦⌊⌋⟧ᵉ ψ φ = ⇓⌊⌋ᵉ {!!} ℂ.⌊ φ ⌋ᵈ

adequacy′ : ∀ {Γ α} (t : Explicit.Tm Γ α) γ (aᴬ : 𝔻.⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ)
          → let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ aᴬ
            in ⟦⌊ t ⌋⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ aᴬ ⌋ᵗ) ∋ (∥ ⌊ γᴬ ⌋ᶜ ∥ , c)
adequacy′ t γ aᴬ =
  let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ aᴬ
      aᴬ′ , aᴬ≤aᴬ′ , φ = 𝐁.cost-existence t γ aᴬ γᴬ {!!}
  in {!!}


-- adequacy : ∀ {Γ α} (t : Explicit.Tm Γ α) γ (aᴬ : 𝔻.⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ)
--          → let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ aᴬ
--            in ∀ γᴬ′
--             → γᴬ 𝔻.≤ᶜ γᴬ′
--             → Σ[ aᴬ′ ∈ 𝔻.⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ ]
--               (aᴬ 𝔻.≤ᵗ aᴬ′ × ⟦⌊ t ⌋⟧ᵉ (⌊ γᴬ′ ⌋ᶜ ⸴ ⌊ aᴬ′ ⌋ᵗ) ∋ (∥ ⌊ γᴬ ⌋ᶜ ∥ , c))
-- adequacy t γ aᴬ γᴬ′ γᴬ≤γᴬ′ =
--   let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ aᴬ
--       aᴬ′ , aᴬ≤aᴬ′ , φ = 𝐁.cost-existence t γ aᴬ γᴬ′ γᴬ≤γᴬ′
--   in aᴬ′ , aᴬ≤aᴬ′ , ℂ⟦⌊⌋⟧ᵉ (ℂ.𝔻≤⇒≤ᶜ γᴬ≤γᴬ′) {!!}

{-
∥ ℂ.⌊ ℂ.𝔻[ γᴬ′ ]ᶜ ⌋ᶜ ∥
All.foldr⁺ _,_ tt
(All.map⁺
 (List.map (ℂ.⟦_⟧⌊_⌋ᵗ x)
  (All.uncurry-const⁻ (List.map (ℂ.𝔻⟦_⟧[_]ᵗ (x .proj₁)) γᴬ′))))

∥ ⌊ γᴬ′ ⌋ᶜ ∥
All.foldr⁺ _,_ tt
(All.map⁺
 (List.map (ℂ.⟦_⟧⌊_⌋ᵗ x)
  (All.uncurry-const⁻ (List.map (ℂ.𝔻⟦_⟧[_]ᵗ (x .proj₁)) γᴬ′))))
-}

  -- ℂ⟦⌊⌋⟧ᵉ (ℂ.𝔻≤⇒≤ᶜ γᴬ≤γᴬ′) φ
  --     φ₁ , φ₂ , φ₃ = 𝐁.cost-existence t γ vᴬ γᴬ {!!}
  -- in {!ℂ⟦⌊ ? ⌋⟧ᵉ!}


-- adequacy : ∀ {Γ α} {t : Explicit.Tm Γ α} {γ} {vᴬ : 𝔻.⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ}
--          → let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ vᴬ
--            in ⟦⌊ t ⌋⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ vᴬ ⌋ᵗ) ∋ (∥ ⌊ γᴬ ⌋ᶜ ∥ , c)
-- adequacy {t = t} {γ = γ} {vᴬ = vᴬ} =
--   let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ vᴬ
--       φ₁ , φ₂ , φ₃ = 𝐁.cost-existence t γ vᴬ γᴬ {!!}
--   in {!ℂ⟦⌊ ? ⌋⟧ᵉ!}

  -- sink (`assert weaken (`pairwise-≲ Γ) `in {!!})

-- ℂ-final : ∀ {Γ α} → Explicit.Tm Γ α → 𝕃.⌊ Γ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- ℂ-final t = final ℂ.⌊ t ⌋ᵉ

-- ⇓ℂ-final : ∀ {v} {v′ : 𝔻.⟦ α ⟧≺ᵉ v}
--          → ℂ.⟦⌊ t ⌋⟧ᵉ γ ∋

-- open import Function
-- final-𝔻 : ∀ {Γ α} {t : Explicit.Tm Γ α} {γ : 𝔼.⟦ Γ ⟧ᶜ} {γᴬ : 𝔻.⟦ Γ ⟧≺ᶜ γ}
--         → let
--         → case γ of λ{
--             (γ′ ⸴ x) → {!!}
--           }

--   → let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ vᴬ
--     in ⟦ ⌊ t ⌋ᵉ ⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ vᴬ ⌋ᵗ) (∥ ⌊ γᴬ ⌋ᶜ ∥ , c)

-- final : ∀ {Γ α}
--       → Explicit.Tm Γ α
--       → (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Γ ⌋ᶜ) ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- final {Γ = Γ} t =
--   `let `free `in
--   `assert (gweakenr ℂ.⌊ t ⌋ᵉ `≟ (` sucᵛ zeroᵛ `, ` zeroᵛ)) `in
--   weaken (weaken (gweakenl {Γ = 𝕃.⌊ Γ ⌋ᶜ} {Δ = 𝕃.⌊ Γ ⌋ᶜ}  `ctx)) `, ` zeroᵛ

-- enclose₁ : ∀ {Γ Δ α τ}
--          → τ ∈ᴸ Γ
--          → 𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Δ ⸴ τ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
--          → 𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Δ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- enclose₁ x t =
--   `let `free `in
--   `assert ` zeroᵛ `≲ ` sucᵛ (sucᵛ (∈-++⁺ʳ _ (∈ᴸ⇒∈ᴸ-map _ x))) `in
--   exchange t

-- -- -- Generate a list of conditions that constrain the input demands.
-- -- constraints : ∀ Γ → List.All (λ α → Γ ⸴ α ⊢ `Bool) Γ
-- -- constraints Γ = List.tabulate (λ x → ` zeroᵛ `≲ ` sucᵛ x)

-- -- -- open import Data.List using ([_])
-- -- -- enclose₁′ : ∀ {Γ Δ α β τ}
-- -- --           → Γ ⸴ τ …⸴ Δ ⸴ β ⊢ α
-- -- --           → Γ …⸴ Δ ⸴ β ⊢ α
-- -- -- enclose₁′ t =
-- -- --   `let `free `in
-- -- --   `assert ` zeroᵛ `≲ ` sucᵛ (sucᵛ {!!}) `in
-- -- --   {!!}

-- -- -- enclose₁′ : 𝕃.⌊ Γ ⌋ᶜ …⸴ (xs₁ ++ [ x ]) ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ →
-- -- --           → 𝕃.⌊ Γ ⌋ᶜ …⸴ xs₁ ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ


-- -- can this be done by introducing a "phantom" context of handled variables?
-- enclose : ∀ {Γ α}
--         → (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Γ ⌋ᶜ) ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
--         → 𝕃.⌊ Γ ⌋ᶜ ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- enclose {Γ = Γ} {α = α} t =
--   List.ind-down ((λ Δ → 𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Δ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ)) t enclose₁

-- -- -- enclose′ : ∀ {Γ α}
-- -- --          → (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Γ ⌋ᶜ) ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- -- --          → 𝕃.⌊ Γ ⌋ᶜ ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- -- -- enclose′ {Γ = Γ} {α = α} t = {!!}
-- -- --   where
-- -- --    x : ∀ Δ → Σ[ Θ ∈ _ ] (Θ …⸴ Δ ≡ Γ) × (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Θ ⌋ᶜ ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ)
-- -- --    x ∅ = {!!}
-- -- --    x (Δ ⸴ τ) = let (Θ , ψ , t′) = x Δ in {!!}
-- -- --  with x Γ where
-- -- --    x : ∀ Δ → Σ[ Θ ∈ _ ] (Θ …⸴ Δ ≡ Γ) × (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Θ ⌋ᶜ ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ)
-- -- --    x ∅ = {!!}
-- -- --    x (Δ ⸴ τ) = let (Θ , ψ , t′) = x Δ in {!!}
-- -- -- ... | Θ , ψ , t′ = {!!}

-- -- -- ... | Θ , ψ , t′ with List.++-identityʳ-unique Γ (sym ψ)
-- -- -- ... | refl = t′


-- --     -- x : ∀ Δ → Σ[ Θ ∈ _ ] Σ[ τ ∈ _ ] (Θ …⸴ Δ ⸴ τ ≡ Γ) × (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Θ ⌋ᶜ ⸴ 𝕃.⌊ α ⌋ᵗ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ)
-- --     -- x ∅ = Γ , {!!} , {!!}
-- --     -- x (Δ ⸴ τ) = let (Θ , τ′ , ψ , t′) = x Δ in Θ , τ , {!!} , {!!}

-- --     -- x = List.ind (λ Δ → Σ[ Θ ∈ _ ] (Θ …⸴ Δ ≡ Γ) × (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Δ ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ)) (Γ , (refl , {!!})) {!!} {!!}
-- -- -- (List.ind {!λ Δ → Σ[ Θ ∈ _ ] (Δ …⸴ Θ ≡ Γ) × (𝕃.⌊ Γ ⌋ᶜ …⸴ 𝕃.⌊ Δ ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ)!} {!!} {!!} {!!})


-- ⌊_⌋ᵉ : ∀ {Γ α}
--      → Explicit.Tm Γ α
--      → 𝕃.⌊ Γ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- ⌊ t ⌋ᵉ = enclose (final t)

-- -- ⌊_⌋ᵉ : ∀ {Γ α}
-- --      → Explicit.Tm Γ α
-- --      → 𝕃.⌊ Γ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
-- -- ⌊ t ⌋ᵉ =
-- --   `let `free `in
-- --   {!!}

-- {-

-- foldl f e (x ∷ xs) = foldl f (f e x) xs

-- -}

-- -- SKETCH OF ADEQUACY
-- --
-- -- By construction, 𝔻⌊ t ⌋ᵉ may evaluate in context (γ, vᴬ) to any value (γᴬ,
-- -- c), provided that γᴬ ≲ γ and also that ℂ⌊ t ⌋ᵉ evaluates to (vᴬ, c) in
-- -- context γᴬ.  In particular, it may evaluate to the minimum such value.

-- {-

-- -- define a data structure/predicate that defines the structure of demand terms
-- -- and operate on it

-- adequacy₁ : γᴬ ≲ γ
--           → ℂ⌊ t ⌋ᵉ γᴬ ∋ (vᴬ, c)
--           → 𝔻⌊ t ⌋ (γ , vᴬ) ∋ (γᴬ , c)

-- adequacy : ∀ {Γ α} {t : Explicit.Tm Γ α} {γ} (vᴬ : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ)
--   → let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ vᴬ
--     in ⟦ ⌊ t ⌋ᵉ ⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ vᴬ ⌋ᵗ) (∥ ⌊ γᴬ ⌋ᶜ ∥ , c)

-- f (c x) = g (f x)
-- f (c x) = f (g x)

-- -}

-- -- data DemandTerm Γ α : _ where


-- adequacy : ∀ {Γ α} {t : Explicit.Tm Γ α} {γ} (vᴬ : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ)
--   → let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ vᴬ
--     in ⟦ ⌊ t ⌋ᵉ ⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ vᴬ ⌋ᵗ) (∥ ⌊ γᴬ ⌋ᶜ ∥ , c)

-- adequacy {t = Explicit.` x} vᴬ = {!!}
-- adequacy {t = Explicit.`let t `in t₁} vᴬ = {!!}
-- adequacy {Γ = ∅} {t = Explicit.`false} {γ = ∅} 𝔻.false = {!!}
-- adequacy {Γ = Γ ⸴ x} {t = Explicit.`false} {γ = v ⸴ γ} vᴬ = {!!}
-- adequacy {t = Explicit.`true} vᴬ = {!!}
-- adequacy {Γ = ∅} {t = Explicit.`if t `then t₁ `else t₂} vᴬ = {!!}
-- adequacy {Γ = Γ ⸴ x} {t = Explicit.`if t `then t₁ `else t₂} vᴬ = {!!}
-- adequacy {t = Explicit.`[]} vᴬ = {!!}
-- adequacy {t = t Explicit.`∷ t₁} vᴬ = {!!}
-- adequacy {t = Explicit.`foldr t t₁ t₂} vᴬ = {!!}
-- adequacy {t = Explicit.`tick t} vᴬ = {!!}
-- adequacy {t = Explicit.`lazy t} vᴬ = {!!}
-- adequacy {t = Explicit.`force t} vᴬ = {!!}

-- -- SKETCH OF SOUNDNESS
-- --
-- -- If 𝔻⌊ t ⌋ evaluates to (γᴬ, c) in context (γ, vᴬ), then γᴬ ≲ γ and ℂ⌊ t ⌋ᵉ
-- -- evaluates to (vᴬ, c) in context γᴬ.

-- -- soundness : ∀ {Γ α} {t : Explicit.Tm Γ α} {γ γᴬ} (vᴬ : 𝔻.⟦ α ⟧≺ᵉ 𝔼.⟦ t ⟧ᵉ γ)
-- --           → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ vᴬ ⌋ᵗ) (γᴬ , c)
-- --           → Σ[ γᴬ′ ∈ _ ] γᴬ ≡ ∥ ⌊ γᴬ′ ⌋ᶜ ∥ × 𝔻.⟦ t ⟧ᵉ γ vᴬ 𝔻.≤ᵐ (γᴬ′ , c)
-- -- soundness = {!!}

-- -- -- ind-down P {xs = x ∷ xs} b s = f x (ind-down P {xs = xs} b s)

-- -- -- soundness: every answer in the demand translation is "above" the answer from
-- -- -- demand semantic








-- -- --   ⟦ ⌊ t ⌋ᵉ ⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ vᴬ ⌋ᵗ) (γᴬ , c)
-- -- -- → (⌈ γᴬ ⌉ , c) ≥ 𝔻.⟦ t ⟧ᵉ γ vᴬ

-- -- -- minimality: the minimal answer in the logic translation is the demand
-- -- -- semantics answer

-- -- -- let (γᴬ , c) = 𝔻.⟦ t ⟧ᵉ γ vᴬ
-- -- -- in ∀ γᴬ′ c′
-- -- --    → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ vᴬ ⌋ᵗ) ∋ (∥ ⌊ γᴬ′ ⌋ᶜ ∥ , c′)
-- -- --    → (∥ ⌊ γᴬ ⌋ᶜ ∥ , c) ≤ (∥ ⌊ γᴬ′ ⌋ᶜ ∥ , c′)
