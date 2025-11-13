module LogicalLaziness.Language.Logic.Equivalence where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
import Data.List.Relation.Unary.All
  as All

open import LogicalLaziness.Language.Explicit
  as Explicit
  using ( `Bool
        ; `T
        ; `List
        )
import LogicalLaziness.Language.Explicit.Semantics.Clairvoyant
  as ℂ

open import LogicalLaziness.Base
import LogicalLaziness.Base.Data.List.All as All
open import LogicalLaziness.Base.Data.List.Membership.Propositional
open import LogicalLaziness.Base.Data.T
open import LogicalLaziness.Base.Data.ListA
  as ListA
  using ( ListA
        ; []
        ; _∷_
        )
open import LogicalLaziness.Language.Logic.Base
open import LogicalLaziness.Language.Logic.Renaming
open import LogicalLaziness.Language.Logic.Construct
open import LogicalLaziness.Language.Logic.Translation

mutual

  ℂ⌊_⌋ᵈ : ∀ {Γ α γ v c}
            {t : Explicit.Tm Γ α}
          → ℂ.⟦ t ⟧ᵉ γ ∋ (v , c)
          → ⟦ ℂ⌊ t ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ ∋ (ℂ⌊ v ⌋ᵗ , c)
  ℂ⌊_⌋ᵈ {γ = γ} (ℂ.⇓ x) = ⇓return (⇓≡ (sym (All.app-lookup {Q = ⟦_⟧ᵗ} x γ ⌊_⌋ᵗ ℂ⌊_⌋ᵗ)) (⇓ ∈ᴸ⇒∈ᴸ-map ⌊_⌋ᵗ x))
  ℂ⌊ ℂ.⇓let φ₁ ⇓in φ₂  ⌋ᵈ = ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ ℂ⌊ φ₂ ⌋ᵈ)
  ℂ⌊ ℂ.⇓false          ⌋ᵈ = ⇓return ⇓false
  ℂ⌊ ℂ.⇓true           ⌋ᵈ = ⇓return ⇓true
  ℂ⌊ ℂ.⇓if φ₁ ⇓then φ₂ ⌋ᵈ = ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ (⇓if ⇓ zeroᵛ ⇓then ⇓weaken ℂ⌊ φ₂ ⌋ᵈ))
  ℂ⌊ ℂ.⇓if φ₁ ⇓else φ₂ ⌋ᵈ = ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ (⇓if ⇓ zeroᵛ ⇓else ⇓weaken ℂ⌊ φ₂ ⌋ᵈ))
  ℂ⌊ ℂ.⇓[]             ⌋ᵈ = ⇓return ⇓[]
  ℂ⌊_⌋ᵈ (ℂ._⇓∷_ {c₂ = c₂} φ₁ φ₂) =
    ⇓>>= (⇓>>=-intro ℂ⌊ φ₁ ⌋ᵈ (⇓[cost+0]
      (⇓>>= (⇓>>=-intro (⇓weaken ℂ⌊ φ₂ ⌋ᵈ) (⇓return (⇓ sucᵛ zeroᵛ ⇓∷ ⇓ zeroᵛ))))))
  ℂ⌊_⌋ᵈ {γ = γ} {v = v} (ℂ.⇓foldr {t₁ = t₁} {t₂ = t₂} {as = as} {c₁ = c₁} {c₂ = c₂} φ₁ φ₂) =
    ⇓>>=
      (⇓>>=-intro
        ℂ⌊ φ₁ ⌋ᵈ
        (⇓foldrM* (⇓ zeroᵛ)
          (⇓foldrM*-weaken
            (subst
              (λ xs → ⟦foldrM* ℂ⌊ t₁ ⌋ᵉ , ℂ⌊ t₂ ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ xs ∋ (ℂ⌊ v ⌋ᵗ , c₂))
              (sym ℂ⌊ as ⌋ᵗ-map) ℂ⌊foldr φ₂ ⌋ᵈ))))
  ℂ⌊ ℂ.⇓tick φ         ⌋ᵈ = ⇓tick ℂ⌊ φ ⌋ᵈ
  ℂ⌊ ℂ.⇓lazy-undefined ⌋ᵈ = ⇓lazily ⇓lazily-undefined
  ℂ⌊ ℂ.⇓lazy-thunk φ   ⌋ᵈ = ⇓lazily (⇓lazily-thunk ℂ⌊ φ ⌋ᵈ)
  ℂ⌊ ℂ.⇓force φ        ⌋ᵈ = ⇓forced (⇓forced-intro ℂ⌊ φ ⌋ᵈ)

  ℂ⌊foldr_⌋ᵈ : ∀ {Γ α β}
                 {t₁ : Explicit.Tm (Γ ⸴ α ⸴ `T β) β}
                 {t₂ : Explicit.Tm Γ β}
                 {γ xs v c}
               → ℂ.⟦foldr t₁ , t₂ ⟧ᵉ γ xs ∋ (v , c)
               → ⟦foldrM* ℂ⌊ t₁ ⌋ᵉ , ℂ⌊ t₂ ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ (ListA.map ℂ⌊_⌋ᵗ xs) ∋ (ℂ⌊ v ⌋ᵗ , c)
  ℂ⌊foldr ℂ.⇓foldr-[] φ                      ⌋ᵈ = foldrM*-[] ℂ⌊ φ ⌋ᵈ
  ℂ⌊foldr ℂ.⇓foldr-∷ ℂ.⇓foldr′-undefined φ   ⌋ᵈ = foldrM*-undefined ℂ⌊ φ ⌋ᵈ
  ℂ⌊foldr ℂ.⇓foldr-∷ (ℂ.⇓foldr′-thunk φ₁) φ₂ ⌋ᵈ = foldrM*-thunk ℂ⌊foldr φ₁ ⌋ᵈ ℂ⌊ φ₂ ⌋ᵈ

var-inv : ∀ {x : α ∈ᴸ Γ} {v} → ⟦ ` x ⟧ᵉ γ ∋ v → v ≡ All.lookup γ x
var-inv (⇓ x) = refl

mutual

  ℂ⌈_⌉ᵈ : ∀ {Γ α} {t : Explicit.Tm Γ α} {γ v c}
        → ⟦ ℂ⌊ t ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ ∋ (ℂ⌊ v ⌋ᵗ , c)
        → ℂ.⟦ t ⟧ᵉ γ ∋ (v , c)
  ℂ⌈_⌉ᵈ {t = Explicit.` x} {γ = γ} {v = v} (⇓return φ)
    rewrite ℂ⌊ trans (var-inv φ) (sym (All.app-lookup x γ ⌊_⌋ᵗ ℂ⌊_⌋ᵗ)) ⌋ᵗ-injective
    = ℂ.⇓ x
  ℂ⌈_⌉ᵈ {t = Explicit.`let t₁ `in t₂} φ
   with ⇑>>= φ
  ... | ⇓>>=-intro {a = a} φ₁ φ₂
   with ℂ⌊ a ⌋ᵗ-surjective
  ... | _ , refl = ℂ.⇓let ℂ⌈ φ₁ ⌉ᵈ ⇓in ℂ⌈ φ₂ ⌉ᵈ
  ℂ⌈_⌉ᵈ {t = Explicit.`false} {v = false} (⇓return ⇓false) = ℂ.⇓false
  ℂ⌈_⌉ᵈ {t = Explicit.`true } {v = true } (⇓return ⇓true ) = ℂ.⇓true
  ℂ⌈_⌉ᵈ {t = Explicit.`if t₁ `then t₂ `else t₃} φ
   with ⇑>>= φ
  ... | ⇓>>=-intro {a = true} φ₁ (⇓if φ₂ ⇓then φ₃) =
    ℂ.⇓if ℂ⌈ φ₁ ⌉ᵈ ⇓then ℂ⌈ ⇑weaken φ₃ ⌉ᵈ
  ... | ⇓>>=-intro {a = false} φ₁ (⇓if φ₂ ⇓else φ₃) =
    ℂ.⇓if ℂ⌈ φ₁ ⌉ᵈ ⇓else ℂ⌈ ⇑weaken φ₃ ⌉ᵈ
  ℂ⌈_⌉ᵈ {t = Explicit.`[]} {v = []} (⇓return ⇓[]) = ℂ.⇓[]
  ℂ⌈_⌉ᵈ {t = t₁ Explicit.`∷ t₂} {v = v} φ
   with ⇑>>= φ
  ... | ⇓>>=-intro {c₁ = c₁} φ₁ φ₂
   with v     | ⇑>>= {t₁ = weaken ℂ⌊ t₂ ⌋ᵉ} {t₂ = `return (` (sucᵛ zeroᵛ) `∷ ` zeroᵛ)} φ₂
  ... | _ ∷ _ | ⇓>>=-intro {c₁ = c₂} {c₂ = c₃} φ₂₁ (⇓return (⇓ _ ⇓∷ ⇓ _)) =
    ℂ.⇓cost≡ (cong (c₁ +_) (sym (+-identityʳ c₂))) (ℂ⌈ φ₁ ⌉ᵈ ℂ.⇓∷ ℂ⌈ ⇑weaken φ₂₁ ⌉ᵈ)
  ℂ⌈_⌉ᵈ {t = Explicit.`foldr t₁ t₂ t₃} {γ = γ} φ with ⇑>>= φ
  ... | ⇓>>=-intro {a = xs} {b = b} φ₁ (⇓foldrA (⇓ _) φ₂)
   with ℂ⌊ xs ⌋ᵗ-surjective
  ... | xs′ , refl =
    ℂ.⇓foldr
      {as = xs′}
      ℂ⌈ φ₁ ⌉ᵈ
      ℂ⌈foldr
        ⇑foldrM*-weaken
          {v = ℂ⌊ xs′ ⌋ᵗ}
          (⇓foldrA⇒⇓foldrM*
            (subst
              (λ xs → ⟦foldrA `transposeF (subsume₂ ℂ⌊ t₁ ⌋ᵉ) , weaken ℂ⌊ t₂ ⌋ᵉ ⟧ᵉ (ℂ⌊ γ ⌋ᶜ ⸴ ℂ⌊ xs′ ⌋ᵗ) xs ∋ _)
              ℂ⌊ xs′ ⌋ᵗ-map
              φ₂)) ⌉ᵈ
  ℂ⌈_⌉ᵈ
    {t = Explicit.`tick t}
    (⇓let φ₁ ⇓in ⇓proj₁ (⇓ _) ⇓, ⇓# 1 ⇓+ ⇓proj₂ (⇓ _))
    = ℂ.⇓tick ℂ⌈ φ₁ ⌉ᵈ
  ℂ⌈_⌉ᵈ {t = Explicit.`lazy t} {v = v} φ
   with v         | ⇑lazily φ
  ... | thunk _   | ⇓lazily-thunk φ′  = ℂ.⇓lazy-thunk ℂ⌈ φ′ ⌉ᵈ
  ... | undefined | ⇓lazily-undefined = ℂ.⇓lazy-undefined
  ℂ⌈_⌉ᵈ {t = Explicit.`force t} φ
   with ⇑forced φ
  ... | ⇓forced-intro φ′ = ℂ.⇓force ℂ⌈ φ′ ⌉ᵈ

  ℂ⌈foldr_⌉ᵈ : ∀ {Γ α β}
                 {t₁ : Explicit.Tm (Γ ⸴ α ⸴ `T β) β}
                 {t₂ : Explicit.Tm Γ β}
                 {γ as b c}
             → ⟦foldrM* ℂ⌊ t₁ ⌋ᵉ , ℂ⌊ t₂ ⌋ᵉ ⟧ᵉ ℂ⌊ γ ⌋ᶜ (ListA.map ℂ⌊_⌋ᵗ as) ∋ (ℂ⌊ b ⌋ᵗ , c)
             → ℂ.⟦foldr t₁ , t₂ ⟧ᵉ γ as ∋ (b , c)
  ℂ⌈foldr_⌉ᵈ {as = []           } (foldrM*-[] φ)        = ℂ.⇓foldr-[] ℂ⌈ φ ⌉ᵈ
  ℂ⌈foldr_⌉ᵈ {as = _ ∷ undefined} (foldrM*-undefined φ) = ℂ.⇓foldr-∷ ℂ.⇓foldr′-undefined ℂ⌈ φ ⌉ᵈ
  ℂ⌈foldr_⌉ᵈ {as = _ ∷ thunk _  } (foldrM*-thunk {v₃ = v₃} φ₁ φ₂)
   with ℂ⌊ v₃ ⌋ᵗ-surjective
  ... | _ , refl = ℂ.⇓foldr-∷ (ℂ.⇓foldr′-thunk ℂ⌈foldr φ₁ ⌉ᵈ) ℂ⌈ φ₂ ⌉ᵈ
