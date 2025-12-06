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
  as All
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

-- ⌈_⌉ᵗ : ∀ {α} {v : 𝔼.⟦ α ⟧ᵗ} 𝕃.⟦⌊ α ⌋⟧ᵗa→ 𝔻.⟦ α ⟧≺ᵗ v → 
-- ⌊ d ⌋ᵗ = ℂ.⌊ ℂ.𝔻[ d ]ᵗ ⌋ᵗ

⌊_⌋ᶜ : ∀ {Γ} {γ : 𝔼.⟦ Γ ⟧ᶜ} → 𝔻.⟦ Γ ⟧≺ᶜ γ → 𝕃.⟦⌊ Γ ⌋⟧ᶜ
⌊_⌋ᶜ {γ = γ} δ = ℂ.⌊ ℂ.𝔻[ δ ]ᶜ ⌋ᶜ

final : Γ ⊢ α `× β
      → Γ ⸴ α ⊢ ∣ Γ ∣ `× β
final t =
  `let (weaken t) `in
  `assert ` sucᵛ zeroᵛ `≟ `proj₁ (` zeroᵛ) `in
  weaken (weaken `env) `, `proj₂ (` zeroᵛ)

⇓final : ∀ {v : ⟦ α ⟧ᵗ} {c}
       → ⟦ t ⟧ᵉ γ ∋ (v , c)
       → ⟦ final t ⟧ᵉ (γ ⸴ v) ∋ (∥ γ ∥ , c)
⇓final φ =
  ⇓let ⇓weaken φ ⇓in
  ⇓assert ⇓≟-true (⇓ sucᵛ zeroᵛ) (⇓proj₁ (⇓ zeroᵛ)) ⇓in
  ⇓weaken (⇓weaken ⇓env) ⇓, ⇓proj₂ (⇓ zeroᵛ)

⇑final : ∀ {v : ⟦ α ⟧ᵗ} {u}
       → ⟦ final t ⟧ᵉ (γ ⸴ v) ∋ (u , c)
       → ∥ γ ∥ ≡ u × ⟦ t ⟧ᵉ γ ∋ (v , c)
⇑final (⇓let φ₁ ⇓in (⇓assert ⇓≟-true φ₂ (⇓proj₁ φ₃) ⇓in φ₄ ⇓, ⇓proj₂ φ₅))
 with ⇑ φ₂ | ⇑ φ₃ | ⇑env (⇑weaken (⇑weaken φ₄)) | ⇑ φ₅
... | refl | refl | refl                        | refl = refl , ⇑weaken φ₁

wrap : Γ ⊢ α `× β
     → Γ ⸴ α ⊢ ∣ Γ ∣ `× β
wrap {Γ = Γ} {α = α} t =
  `let-free* Γ `in
  `assert gweakenl Γ `env `≲ gweakenr Γ (weaken `env)
  `in sink Γ (gweakenl (Γ ⸴ α) (final t))

⇓wrap : ∀ {γ′ : ⟦ Γ ⟧ᶜ} {v : ⟦ α ⟧ᵗ}
      → γ′ ≲ᶜ γ
      → ⟦ t ⟧ᵉ γ′ ∋ (v , c)
      → ⟦ wrap t ⟧ᵉ (γ ⸴ v) ∋ (∥ γ′ ∥ , c)
⇓wrap {γ = γ} {γ′ = γ′} {v = v} ψ φ =
  ⇓let-free* γ′ ⇓in
  ⇓assert ⇓≲-true (⇓gweakenl γ′ ⇓env) (⇓gweakenr γ′ (⇓weaken ⇓env)) (≲ᶜ⇒≲ᵗ ψ) ⇓in
  ⇓sink γ′ (⇓gweakenl (γ′ ⸴ v) (⇓final φ))

⇑wrap : ∀ {v : ⟦ α ⟧ᵗ} {u}
      → ⟦ wrap t ⟧ᵉ (γ ⸴ v) ∋ (u , c)
      → Σ[ γ′ ∈ ⟦ Γ ⟧ᶜ ] ∥ γ′ ∥ ≡ u × γ′ ≲ᶜ γ × ⟦ t ⟧ᵉ γ′ ∋ (v , c)
⇑wrap {Γ = Γ} {v = v} φ
 with ⇑let-free* Γ ⇑in φ
... | γ′ , (⇓assert ⇓≲-true φ₁ φ₂ ψ ⇓in φ₃)
 with ⇑env (⇑gweakenl γ′ φ₁)
    | ⇑env (⇑weaken (⇑gweakenr γ′ φ₂))
    | ⇑final (⇑gweakenl (γ′ ⸴ v) (⇑sink γ′ φ₃))
... | refl | refl | refl , φ₃′ = _ , refl , ≲ᵗ⇒≲ᶜ ψ , φ₃′

⌊_⌋ᵉ : ∀ {Γ α}
     → Explicit.Tm Γ α
     → 𝕃.⌊ Γ ⸴ α ⌋ᶜ ⊢ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ `× `ℕ
⌊ t ⌋ᵉ = wrap ℂ.⌊ t ⌋ᵉ

⟦⌊_⌋⟧ᵉ : ∀ {Γ α} (t : Explicit.Tm Γ α)
       → 𝕃.⟦⌊ Γ ⸴ α ⌋⟧ᶜ → Tick ⟦ ∣ 𝕃.⌊ Γ ⌋ᶜ ∣ ⟧ᵗ → Type
⟦⌊ t ⌋⟧ᵉ = ⟦ ⌊ t ⌋ᵉ ⟧ᵉ

⇓⌊_,_⌋ᵉ : ∀ {Γ α} {t : Explicit.Tm Γ α}
            {γ γᴬ : 𝕃.⟦⌊ Γ ⌋⟧ᶜ} {vᴬ c}
        → γᴬ ≲ᶜ γ
        → ℂ.⟦⌊ t ⌋⟧ᵉ γᴬ ∋ (vᴬ , c)
        → ⟦⌊ t ⌋⟧ᵉ (γ ⸴ vᴬ) ∋ (∥ γᴬ ∥ , c)
⇓⌊ ψ , φ ⌋ᵉ = ⇓wrap ψ φ

⇑⌊_⌋ᵉ : ∀ {Γ α} {t : Explicit.Tm Γ α}
          {γ : 𝕃.⟦⌊ Γ ⌋⟧ᶜ} {vᴬ u c}
        → ⟦⌊ t ⌋⟧ᵉ (γ ⸴ vᴬ) ∋ (u , c)
        → Σ[ γᴬ ∈ 𝕃.⟦⌊ Γ ⌋⟧ᶜ ] ∥ γᴬ ∥ ≡ u × γᴬ ≲ᶜ γ × ℂ.⟦⌊ t ⌋⟧ᵉ γᴬ ∋ (vᴬ , c)
⇑⌊ φ ⌋ᵉ = ⇑wrap φ

ℂ⇓⌊_,_⌋ᵉ : ∀ {Γ α} {t : Explicit.Tm Γ α}
             {γ γᴬ aᴬ c}
         → γᴬ ℂ.≤ᶜ γ
         → ℂ.⟦ t ⟧ᵉ γᴬ ∋ (aᴬ , c)
         → ⟦⌊ t ⌋⟧ᵉ (ℂ.⌊ γ ⌋ᶜ ⸴ ℂ.⌊ aᴬ ⌋ᵗ) ∋ (∥ ℂ.⌊ γᴬ ⌋ᶜ ∥ , c)
ℂ⇓⌊ ψ , φ ⌋ᵉ = ⇓⌊ ℂ.⌊ ψ ⌋≤ᶜ , ℂ.⌊ φ ⌋ᵈ ⌋ᵉ

ℂ⇑⌊_⌋ᵉ : ∀ {Γ α} {t : Explicit.Tm Γ α}
           {γ aᴬ u c}
       → ⟦⌊ t ⌋⟧ᵉ (ℂ.⌊ γ ⌋ᶜ ⸴ ℂ.⌊ aᴬ ⌋ᵗ) ∋ (u , c)
       → Σ[ γᴬ ∈ _ ] u ≡ ∥ ℂ.⌊ γᴬ ⌋ᶜ ∥ × γᴬ ℂ.≤ᶜ γ × ℂ.⟦ t ⟧ᵉ γᴬ ∋ (aᴬ , c)
ℂ⇑⌊ φ ⌋ᵉ with ⇑⌊ φ ⌋ᵉ
... | γᴬ , refl , ψ , φ′ rewrite sym ℂ.⌊⌈ γᴬ ⌉⌋ᶜ = ℂ.⌈ γᴬ ⌉ᶜ , refl , ℂ.⌈ ψ ⌉≤ᶜ , ℂ.⌈ φ′ ⌉ᵈ

adequacy : ∀ {Γ α} (t : Explicit.Tm Γ α) γ (aᴬ : 𝔻.⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ)
         → let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ aᴬ
           in ∀ γᴬ′
            → γᴬ 𝔻.≤ᶜ γᴬ′
            → Σ[ aᴬ′ ∈ 𝔻.⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ ] (aᴬ 𝔻.≤ᵗ aᴬ′ × ⟦⌊ t ⌋⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ aᴬ′ ⌋ᵗ) ∋ (∥ ⌊ γᴬ′ ⌋ᶜ ∥ , c))
adequacy t γ aᴬ γᴬ′ γᴬ≤γᴬ′ =
  let γᴬ , c = 𝔻.⟦ t ⟧ᵉ γ aᴬ
      aᴬ′ , aᴬ≤aᴬ′ , φ = 𝐁.cost-existence t γ aᴬ γᴬ′ γᴬ≤γᴬ′
  in aᴬ′ , aᴬ≤aᴬ′ , ℂ⇓⌊ ℂ.𝔻≤𝔼ᶜ γᴬ′ , φ ⌋ᵉ

soundness : ∀ {Γ α} (t : Explicit.Tm Γ α) γ (aᴬ : 𝔻.⟦ α ⟧≺ᵗ 𝔼.⟦ t ⟧ᵉ γ) γᴬ
          → ⟦ ⌊ t ⌋ᵉ ⟧ᵉ (𝔼.⌊ γ ⌋ᶜ ⸴ ⌊ aᴬ ⌋ᵗ) (γᴬ , c)
          → Σ[ γᴬ′ ∈ _ ] γᴬ ≡ ∥ ⌊ γᴬ′ ⌋ᶜ ∥ × 𝔻.⟦ t ⟧ᵉ γ aᴬ 𝔻.≤ᵐ (γᴬ′ , c)
soundness t γ aᴬ γᴬ φ with ℂ⇑⌊ φ ⌋ᵉ
... | γᴬ′ , refl , ψ₂ , φ′ rewrite sym (ℂ.𝔻𝔼ᶜ ψ₂) =
  let ψ₃ , ψ₄ = 𝐁.cost-minimality γ aᴬ φ′
  in ℂ.≤𝔼⇒𝔻≺ᶜ ψ₂ , refl , ψ₃ , ψ₄
