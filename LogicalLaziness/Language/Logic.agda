module LogicalLaziness.Language.Logic where

open import Agda.Builtin.FromNat

open import Effect.Monad.Writer
open import Function
  hiding (_∋_)
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Unit
  using (⊤)
open import Data.Bool
  as Bool
  using (Bool; false; true)
open import Data.Bool.Instances
open import Data.Nat
  as ℕ
  using (ℕ; _+_)
open import Data.Product
  as Σ
open import Data.Product.Properties
  as Σ
open import Data.List
  as List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All

open import LogicalLaziness.Base
open import LogicalLaziness.Base.T
  as T
open import LogicalLaziness.Base.ListA
  as ListA
open import LogicalLaziness.Language.Demand
  as Demand
  hiding ( Ty
         ; Ctx
         ; _⊢_
         ; `_
         ; `let_`in_
         ; `false
         ; `true
         ; `if_`then_`else_
         ; `[]
         ; _`∷_
         ; `foldr
         ; `tick
         ; `lazy
         ; `force
         )

infixr 5 _`×_
data Ty : Type where
  `Bool  : Ty
  _`×_   : Ty → Ty → Ty
  `T     : Ty → Ty
  `ℕ     : Ty
  `ListA : Ty → Ty

variable
  α β τ τ₁ τ₂ : Ty

Ctx : Type
Ctx = List Ty

variable
  Γ Δ : Ctx

infix  1.59  `_ #_
infixl 1.56  _`+_
infixr 1.55  _`∷_
infixr 1.54  _`,_
infix  1.54  _`≟_ _`≲_
infixr 1.51  _`?_ _`>>=_
infix  1.505 `if_`then_`else_ `if_`then_ `if_`else_ `assert_`in_
infix  1.50  `let_`in_

infix 4 _⊢_
data _⊢_ : Ctx → Ty → Type where

  `_               : τ ∈ᴸ Γ → Γ ⊢ τ

  `let_`in_        : Γ ⊢ α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β

  `false           : Γ ⊢ `Bool
  `true            : Γ ⊢ `Bool

  `if_`then_`else_ : Γ ⊢ `Bool
                   → Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ τ

  _`≟_             : Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ `Bool

  _`≲_             : Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ `Bool

  _`,_             : Γ ⊢ α
                   → Γ ⊢ β
                   → Γ ⊢ α `× β

  `fst             : Γ ⊢ α `× β
                   → Γ ⊢ α

  `snd             : Γ ⊢ α `× β
                   → Γ ⊢ β

  `undefined       : Γ ⊢ `T τ

  `thunk           : Γ ⊢ τ
                   → Γ ⊢ `T τ

  `T-case          : Γ ⊢ `T α
                   → Γ ⸴ α ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ β

  #_               : ℕ → Γ ⊢ `ℕ

  _`+_             : Γ ⊢ `ℕ
                   → Γ ⊢ `ℕ
                   → Γ ⊢ `ℕ

  `[]              : Γ ⊢ `ListA τ

  _`∷_             : Γ ⊢ `T τ
                   → Γ ⊢ `T (`ListA τ)
                   → Γ ⊢ `ListA τ

  `foldrA          : Γ ⸴ `T α ⸴ β ⊢ β
                   → Γ ⊢ β
                   → Γ ⊢ `ListA α
                   → Γ ⊢ β

  `free            : Γ ⊢ τ

  _`?_             : Γ ⊢ τ
                   → Γ ⊢ τ
                   → Γ ⊢ τ

  `fail            : Γ ⊢ τ

variable
  t t₁ t₂ t₃ : Γ ⊢ τ

instance
  Number-ℕ : Number ℕ
  Number-ℕ = record
    { Constraint = const ⊤
    ; fromNat    = λ n → n
    }

  Number-Tm : ∀ {Γ} → Number (Γ ⊢ `ℕ)
  Number-Tm = record
    { Constraint = const ⊤
    ; fromNat    = λ n → # n
    }

Ty⟦_⟧ : Ty → Type
Ty⟦ `Bool    ⟧ = Bool
Ty⟦ α `× β   ⟧ = Ty⟦ α ⟧ × Ty⟦ β ⟧
Ty⟦ `T α     ⟧ = T Ty⟦ α ⟧
Ty⟦ `ℕ       ⟧ = ℕ
Ty⟦ `ListA α ⟧ = ListA Ty⟦ α ⟧

Ty-≡-dec : DecidableEquality Ty⟦ τ ⟧
Ty-≡-dec {`Bool}    = Bool._≟_
Ty-≡-dec {α `× β}   = Σ.≡-dec Ty-≡-dec Ty-≡-dec
Ty-≡-dec {`T τ}     = T.≡-dec Ty-≡-dec
Ty-≡-dec {`ℕ}       = ℕ._≟_
Ty-≡-dec {`ListA τ} = ListA.≡-dec Ty-≡-dec

Ctx⟦_⟧ : Ctx → Type
Ctx⟦_⟧ = All Ty⟦_⟧

variable
  g γ : Ctx⟦ Γ ⟧

---------------
-- Renamings --
---------------

infix 4 _→ʳ_
_→ʳ_ : Ctx → Ctx → Type
Γ →ʳ Δ = ∀ {τ} → τ ∈ᴸ Γ → τ ∈ᴸ Δ

variable
  ρ : Γ →ʳ Δ

↑ʳ_ : Γ →ʳ Δ → Γ ⸴ τ →ʳ Δ ⸴ τ
↑ʳ_ ρ zeroᵛ    = zeroᵛ
↑ʳ_ ρ (sucᵛ x) = sucᵛ (ρ x)

infixr -1 _$ʳ_
_$ʳ_ : Γ →ʳ Δ → Γ ⊢ τ → Δ ⊢ τ
ρ $ʳ ` x                      = ` ρ x
ρ $ʳ `let t₁ `in t₂           = `let (ρ $ʳ t₁) `in (↑ʳ ρ $ʳ t₂)
ρ $ʳ `false                   = `false
ρ $ʳ `true                    = `true
ρ $ʳ `if t₁ `then t₂ `else t₃ = `if (ρ $ʳ t₁) `then ρ $ʳ t₂ `else (ρ $ʳ t₃)
ρ $ʳ t₁ `≟ t₂                 = (ρ $ʳ t₁) `≟ (ρ $ʳ t₂)
ρ $ʳ t₁ `≲ t₂                 = (ρ $ʳ t₁) `≲ (ρ $ʳ t₂)
ρ $ʳ t₁ `, t₂                 = (ρ $ʳ t₁) `, (ρ $ʳ t₂)
ρ $ʳ `fst t₁                  = `fst (ρ $ʳ t₁)
ρ $ʳ `snd t₁                  = `snd (ρ $ʳ t₁)
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

↑ᵗ_ : Γ ⊢ α → Γ ⸴ τ ⊢ α
↑ᵗ_ = (sucᵛ $ʳ_)

exchange : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
exchange t = ρ′ $ʳ t
  where
    ρ′ : α ∈ᴸ Γ ⸴ τ₁ ⸴ τ₂ → α ∈ᴸ Γ ⸴ τ₂ ⸴ τ₁
    ρ′ (here px) = there (here px)
    ρ′ (sucᵛ (here px)) = here px
    ρ′ (sucᵛ (sucᵛ p)) = there (there p)

-- A common special-case context manipulation.
subsume1 : Γ ⸴ τ₁ ⊢ α → Γ ⸴ τ₂ ⸴ τ₁ ⊢ α
subsume1 t = exchange (↑ᵗ t)

-------------------
-- Substitutions --
-------------------

infix 4 _→ˢ_
_→ˢ_ : Ctx → Ctx → Type
_→ˢ_ Γ Δ = ∀ {τ} → τ ∈ᴸ Γ → Δ ⊢ τ

↑ˢ_ : Γ →ˢ Δ → Γ ⸴ τ →ˢ Δ ⸴ τ
(↑ˢ σ) zeroᵛ     = ` zeroᵛ
(↑ˢ σ) (sucᵛ x) = ↑ᵗ σ x

infixr -1 _$ˢ_
_$ˢ_ : Γ →ˢ Δ → Γ ⊢ τ → Δ ⊢ τ
σ $ˢ ` x                      = σ x
σ $ˢ `let t₁ `in t₂           = `let (σ $ˢ t₁) `in (↑ˢ σ $ˢ t₂)
σ $ˢ `false                   = `false
σ $ˢ `true                    = `true
σ $ˢ `if t₁ `then t₂ `else t₃ = `if (σ $ˢ t₁) `then (σ $ˢ t₂) `else (σ $ˢ t₃)
σ $ˢ t₁ `≟ t₂                 = (σ $ˢ t₁) `≟ (σ $ˢ t₂)
σ $ˢ t₁ `≲ t₂                 = (σ $ˢ t₁) `≲ (σ $ˢ t₂)
σ $ˢ t₁ `, t₂                 = (σ $ˢ t₁) `, (σ $ˢ t₂)
σ $ˢ `fst t₁                  = `fst (σ $ˢ t₁)
σ $ˢ `snd t₁                  = `snd (σ $ˢ t₁)
σ $ˢ `undefined               = `undefined
σ $ˢ `thunk t₁                = `thunk (σ $ˢ t₁)
σ $ˢ `T-case t₁ t₂ t₃         = `T-case (σ $ˢ t₁) (↑ˢ σ $ˢ t₂) (σ $ˢ t₃)
σ $ˢ (# n)                    = # n
σ $ˢ t₁ `+ t₂                 = (σ $ˢ t₁) `+ (σ $ˢ t₂)
σ $ˢ `[]                      = `[]
σ $ˢ t₁ `∷ t₂                 = (σ $ˢ t₁) `∷ (σ $ˢ t₂)
σ $ˢ `foldrA t₁ t₂ t₃         = `foldrA (↑ˢ ↑ˢ σ $ˢ t₁) (σ $ˢ t₂) (σ $ˢ t₃)
σ $ˢ `free                    = `free
σ $ˢ t₁ `? t₂                 = (σ $ˢ t₁) `? (σ $ˢ t₂)
σ $ˢ `fail                    = `fail

--------------------
-- Approximations --
--------------------

data Ty⟦_⟧[_≲_] : ∀ α → Ty⟦ α ⟧ → Ty⟦ α ⟧ → Type where
  ≲-Bool : ∀ {v} → Ty⟦ `Bool ⟧[ v ≲ v ]
  ≲-undefined : ∀ {v} → Ty⟦ `T α ⟧[ undefined ≲ v ]
  ≲-thunk : ∀ {v₁ v₂} → Ty⟦ α ⟧[ v₁ ≲ v₂ ] → Ty⟦ `T α ⟧[ thunk v₁ ≲ thunk v₂ ]
  ≲-[] : Ty⟦ `ListA α ⟧[ [] ≲ [] ]
  ≲-∷ : ∀ {v₁ vs₁ v₂ vs₂} → Ty⟦ `T α ⟧[ v₁ ≲ v₂ ] → Ty⟦ `T (`ListA α) ⟧[ vs₁ ≲ vs₂ ] →
    Ty⟦ `ListA α ⟧[ v₁ ∷ vs₁ ≲ v₂ ∷ vs₂ ]

_≲?_ : ∀ {α} → Decidable Ty⟦ α ⟧[_≲_]
_≲?_ {`Bool} v₁ v₂ with v₁ ≟ v₂
... | yes refl = yes ≲-Bool
... | no p = no (λ{ ≲-Bool → p refl})
_≲?_ {τ₁ `× τ₂} v₁ v₂ = no (λ ())
_≲?_ {`T τ₁} (thunk x) (thunk x₁) with x ≲? x₁
... | yes p = yes (≲-thunk p)
... | no p = no (λ{ (≲-thunk x₂) → p x₂})
_≲?_ {`T τ₁} (thunk x) undefined = no (λ ())
_≲?_ {`T τ₁} undefined (thunk x) = yes ≲-undefined
_≲?_ {`T τ₁} undefined undefined = yes ≲-undefined
_≲?_ {`ℕ} v₁ v₂ = no (λ ())
_≲?_ {`ListA α} [] [] = yes ≲-[]
_≲?_ {`ListA α} [] (_ ∷ _) = no (λ ())
_≲?_ {`ListA α} (_ ∷ _) [] = no (λ ())
_≲?_ {`ListA α} (x ∷ xs) (y ∷ ys) = {!!}

----------------
-- Evaluation --
----------------

data foldrA⟦_,_,_⟧
    (P : Ctx⟦ Γ ⸴ `T α ⸴ β ⟧ → Ty⟦ β ⟧ → Type)
    (e : Ty⟦ β ⟧) :
    T (ListA Ty⟦ α ⟧) →
    Ctx⟦ Γ ⟧ →
    Ty⟦ β ⟧ →
    Type where
  foldrA-undefined : foldrA⟦ P , e , undefined ⟧ g ∋ e
  foldrA-[]        : foldrA⟦ P , e , thunk []  ⟧ g ∋ e
  foldrA-∷         : ∀ {b b′ a as} →
    foldrA⟦ P , e , as ⟧ g ∋ b →
    P (g ⸴ a ⸴ b) ∋ b′ →
    foldrA⟦ P , e , thunk (a ∷ as) ⟧ g ∋ b′

data ⟦_⟧ᵉ : ∀ {Γ τ} → Γ ⊢ τ → Ctx⟦ Γ ⟧ → Ty⟦ τ ⟧ → Type where
  `_                : (x : τ ∈ᴸ Γ) → ⟦ ` x ⟧ᵉ g (All.lookup g x)
  `let_`in_         : ∀ {v₁ v₂} →
    ⟦ t₁ ⟧ᵉ g ∋ v₁ →
    ⟦ t₂ ⟧ᵉ (g ⸴ v₁) ∋ v₂ →
    ⟦ `let t₁ `in t₂ ⟧ᵉ g ∋ v₂
  `false            : ⟦ `false ⟧ᵉ g ∋ false
  `true             : ⟦ `true ⟧ᵉ g ∋ true
  `if_`else_ : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ false →
    ⟦ t₃ ⟧ᵉ g ∋ v →
    ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g ∋ v
  `if_`then_ : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ true →
    ⟦ t₂ ⟧ᵉ g ∋ v →
    ⟦ `if t₁ `then t₂ `else t₃ ⟧ᵉ g ∋ v
  `≟-true : {v : Ty⟦ τ ⟧} →
    ⟦ t₁ ⟧ᵉ g ∋ v →
    ⟦ t₂ ⟧ᵉ g ∋ v →
    ⟦ t₁ `≟ t₂ ⟧ᵉ g ∋ true
  -- eval-≲ : ∀ {v₁ v₂ : Ty⟦ α ⟧} →
  --   ⟦ t₁ ⟧ᵉ g ∋ v₁ →
  --   ⟦ t₂ ⟧ᵉ g ∋ v₂ →
  --   ⟦ t₁ `≲ t₂ ⟧ᵉ g (does (v₁ ≲? v₂))
  `≲-true : {v₁ v₂ : Ty⟦ τ ⟧} →
    ⟦ t₁ ⟧ᵉ g ∋ v₁ →
    ⟦ t₂ ⟧ᵉ g ∋ v₂ →
    Ty⟦ τ ⟧[ v₁ ≲ v₂ ] →
    ⟦ t₁ `≲ t₂ ⟧ᵉ g ∋ true
  _`,_              : ∀ {v₁ v₂} →
    ⟦ t₁ ⟧ᵉ g ∋ v₁ →
    ⟦ t₂ ⟧ᵉ g ∋ v₂ →
    ⟦ t₁ `, t₂ ⟧ᵉ g ∋ (v₁ , v₂)
  `proj1 : ∀ {v} →
    ⟦ t ⟧ᵉ g ∋ v →
    ⟦ `fst t ⟧ᵉ g ∋ proj₁ v
  `proj2 : ∀ {v}
    → ⟦ t ⟧ᵉ g v
    → ⟦ `snd t ⟧ᵉ g ∋ proj₂ v
  `undefined : ⟦ `undefined {τ = τ} ⟧ᵉ g ∋ undefined
  `thunk : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ v →
    ⟦ `thunk t₁ ⟧ᵉ g ∋ thunk v
  `T-case-undefined : ∀ {v} →
    ⟦ t₁ ⟧ᵉ g ∋ undefined →
    ⟦ t₃ ⟧ᵉ g ∋ v →
    ⟦ `T-case t₁ t₂ t₃ ⟧ᵉ g ∋ v
  `T-case-thunk     : ∀ {v₁ v₂} →
    ⟦ t₁ ⟧ᵉ g ∋ thunk v₁ →
    ⟦ t₂ ⟧ᵉ (g ⸴ v₁) ∋ v₂ →
    ⟦ `T-case t₁ t₂ t₃ ⟧ᵉ g ∋ v₂
  #_                : ∀ n → ⟦ # n ⟧ᵉ g n
  _`+_              : ∀ {n₁ n₂} →
    ⟦ t₁ ⟧ᵉ g ∋ n₁ →
    ⟦ t₂ ⟧ᵉ g ∋ n₂ →
    ⟦ t₁ `+ t₂ ⟧ᵉ g ∋ (n₁ + n₂)
  `[]               : ∀ {τ} → ⟦_⟧ᵉ {τ = `ListA τ} `[] g []
  _`∷_              : ∀ {x xs} → ⟦ t₁ ⟧ᵉ g x → ⟦ t₂ ⟧ᵉ g xs → ⟦ t₁ `∷ t₂ ⟧ᵉ g (x ∷ xs)
  `foldrA           : ∀ {e xs b} →
    ⟦ t₂ ⟧ᵉ g e →
    ⟦ t₃ ⟧ᵉ g xs →
    foldrA⟦ ⟦ t₁ ⟧ᵉ , e , thunk xs ⟧ g ∋ b →
    ⟦ `foldrA t₁ t₂ t₃ ⟧ᵉ g b
  `free             : ∀ {v : Ty⟦ α ⟧} → ⟦ `free ⟧ᵉ g v
  ?l                : ∀ {x} → ⟦ t₁ ⟧ᵉ g x → ⟦ t₁ `? t₂ ⟧ᵉ g x
  ?r                : ∀ {x} → ⟦ t₂ ⟧ᵉ g x → ⟦ t₁ `? t₂ ⟧ᵉ g x

-- eval-≲-true : ∀ {v₁ v₂ : Ty⟦ α ⟧} →
--   ⟦ t₁ ⟧ᵉ g ∋ v₁ →
--   ⟦ t₂ ⟧ᵉ g ∋ v₂ →
--   Ty⟦ α ⟧[ v₁ ≲ v₂ ] →
--   ⟦ t₁ `≲ t₂ ⟧ᵉ g true
-- eval-≲-true {v₁ = v₁} {v₂} p q r with v₁ ≲? v₂
-- ... | yes s = subst (⟦ _ `≲ _ ⟧ᵉ _) (dec-true _ s) (eval-≲ p q)
-- ... | no s = contradiction r s

weaken-eval :
  ∀ {Γ α τ} {t : Γ ⊢ τ} {g : Ctx⟦ Γ ⟧} {a : Ty⟦ α ⟧}
    {v : Ty⟦ τ ⟧}
  → ⟦ t ⟧ᵉ g v
  → ⟦ ↑ᵗ t ⟧ᵉ (g ⸴ a) v
weaken-eval (` x) = ` sucᵛ x
weaken-eval (`let φ₁ `in φ₂) = `let weaken-eval φ₁ `in {!!}
weaken-eval `false = `false
weaken-eval `true = `true
weaken-eval (`if φ₁ `else φ₂) = `if weaken-eval φ₁ `else weaken-eval φ₂
weaken-eval (`if φ₁ `then φ₂) = `if weaken-eval φ₁ `then weaken-eval φ₂
weaken-eval (`≟-true φ₁ φ₂) = `≟-true (weaken-eval φ₁) (weaken-eval φ₂)
weaken-eval (`≲-true φ₁ φ₂ ψ) = `≲-true (weaken-eval φ₁) (weaken-eval φ₂) ψ
weaken-eval (φ₁ `, φ₂) = weaken-eval φ₁ `, weaken-eval φ₂
weaken-eval (`proj1 φ₁) = `proj1 (weaken-eval φ₁)
weaken-eval (`proj2 φ₁) = `proj2 (weaken-eval φ₁)
weaken-eval `undefined = `undefined
weaken-eval (`thunk φ₁) = `thunk (weaken-eval φ₁)
weaken-eval (`T-case-thunk φ₁ φ₂) = `T-case-thunk (weaken-eval φ₁) {!weaken-eval φ₂!}
weaken-eval (`T-case-undefined φ₁ φ₂) = `T-case-undefined (weaken-eval φ₁) (weaken-eval φ₂)
weaken-eval (# n) = # n
weaken-eval (φ₁ `+ φ₂) = weaken-eval φ₁ `+ weaken-eval φ₂
weaken-eval `[] = `[]
weaken-eval (φ₁ `∷ φ₂) = weaken-eval φ₁ `∷ weaken-eval φ₂
weaken-eval (`foldrA e e₁ x) = {!!}
weaken-eval `free = `free
weaken-eval (?l φ₁) = ?l (weaken-eval φ₁)
weaken-eval (?r φ₁) = ?r (weaken-eval φ₁)

exchange-eval :
  ∀ {Γ α τ₁ τ₂} {t : Γ ⸴ τ₁ ⸴ τ₂ ⊢ α} {g : Ctx⟦ Γ ⟧} {a : Ty⟦ α ⟧}
    {v₁ : Ty⟦ τ₁ ⟧} {v₂ : Ty⟦ τ₂ ⟧}
  → ⟦ t ⟧ᵉ (g ⸴ v₁ ⸴ v₂) a
  → ⟦ exchange t ⟧ᵉ (g ⸴ v₂ ⸴ v₁) a
exchange-eval = {!!}

-----------------
-- Translation --
-----------------

Ty⟦_⟧ₜ : Demand.Ty → Ty
Ty⟦ Demand.`Bool   ⟧ₜ = `Bool
Ty⟦ Demand.`T τ    ⟧ₜ = `T Ty⟦ τ ⟧ₜ
Ty⟦ Demand.`List τ ⟧ₜ = `ListA Ty⟦ τ ⟧ₜ

Ctx⟦_⟧ₜ : Demand.Ctx → Ctx
Ctx⟦ γ ⟧ₜ = List.map Ty⟦_⟧ₜ γ

`assert_`in_ : Γ ⊢ `Bool → Γ ⊢ τ → Γ ⊢ τ
`assert t₁ `in t₂ = `if t₁ `then t₂ `else `fail

`eval-assert_`in_ : ∀ {v} →
  ⟦ t₁ ⟧ᵉ g ∋ true →
  ⟦ t₂ ⟧ᵉ g ∋ v →
  ⟦ `assert t₁ `in t₂ ⟧ᵉ g ∋ v
`eval-assert_`in_ δ₁ δ₂ = `if δ₁ `then δ₂

`force : Γ ⊢ `T τ → Γ ⊢ τ
`force t = `T-case t (` zeroᵛ) `fail

`M : Ty → Ty
`M τ = τ `× `ℕ

_`>>=_ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → Γ ⊢ `M β
t₁ `>>= t₂ =
  `let t₁ `in
  `let (`let `fst (` zeroᵛ) `in subsume1 t₂) `in
  (`fst (` zeroᵛ) `, (`snd (` (sucᵛ zeroᵛ)) `+ `snd (` zeroᵛ)))

`fmap : (∀ {Δ} → Δ ⊢ α → Δ ⊢ β) → Γ ⊢ `M α → Γ ⊢ `M β
`fmap f t = `let t `in f (`fst (` zeroᵛ)) `, `snd (` zeroᵛ)

`return : Γ ⊢ τ → Γ ⊢ `M τ
`return t = t `, 0

⟦_⟧ᵉₜ : ∀ {Γ τ} → Demand.Tm Γ τ → Ctx⟦ Γ ⟧ₜ ⊢ `M Ty⟦ τ ⟧ₜ
⟦ Demand.` x ⟧ᵉₜ                      = `return (` (∈ᴸ⇒∈ᴸ-map Ty⟦_⟧ₜ x))
⟦ Demand.`let t₁ `in t₂ ⟧ᵉₜ           = ⟦ t₁ ⟧ᵉₜ `>>= ⟦ t₂ ⟧ᵉₜ
⟦ Demand.`false ⟧ᵉₜ                   = `return `false
⟦ Demand.`true ⟧ᵉₜ                    = `return `true
⟦ Demand.`if t₁ `then t₂ `else t₃ ⟧ᵉₜ =
  ⟦ t₁ ⟧ᵉₜ `>>=
  (`if ` zeroᵛ `then ↑ᵗ ⟦ t₂ ⟧ᵉₜ `else ↑ᵗ ⟦ t₃ ⟧ᵉₜ)
⟦ Demand.`[] ⟧ᵉₜ                      = `return `[]
⟦ t₁ Demand.`∷ t₂ ⟧ᵉₜ                 =
  ⟦ t₁ ⟧ᵉₜ `>>=
  ↑ᵗ ⟦ t₂ ⟧ᵉₜ `>>=
  `return (` sucᵛ zeroᵛ `∷ ` zeroᵛ)
⟦ Demand.`foldr t₁ t₂ t₃ ⟧ᵉₜ          = ⟦ t₂ ⟧ᵉₜ
⟦ Demand.`tick t₁ ⟧ᵉₜ                 = ⟦ t₁ ⟧ᵉₜ
⟦ Demand.`lazy t₁ ⟧ᵉₜ                 = `fmap `thunk ⟦ t₁ ⟧ᵉₜ `? `return `undefined
⟦ Demand.`force t₁ ⟧ᵉₜ                = `fmap `force ⟦ t₁ ⟧ᵉₜ

-- Ctx⟦_⟧ₜ : ∀ {Γ} → Demand.Ctx⟦ Γ ⟧ₑ → Ctx⟦ 

⟦_⟧ᵉₐ : ∀ {τ v} → 𝔻⟦ τ ⟧ᵗ≺ v → Ty⟦ Ty⟦ τ ⟧ₜ ⟧
⟦_⟧ᵉₐ {Demand.`Bool}   (𝔻⟦_⟧ᵗ≺_.↓Bool {v}) = v
⟦_⟧ᵉₐ {Demand.`T τ}    (𝔻⟦_⟧ᵗ≺_.thunk v) = thunk ⟦ v ⟧ᵉₐ 
⟦_⟧ᵉₐ {Demand.`T τ}    𝔻⟦_⟧ᵗ≺_.undefined = undefined
⟦_⟧ᵉₐ {Demand.`List τ} 𝔻⟦_⟧ᵗ≺_.[] = []
⟦_⟧ᵉₐ {Demand.`List τ} (v 𝔻⟦_⟧ᵗ≺_.∷ v₁) = ⟦ v ⟧ᵉₐ ∷ ⟦ v₁ ⟧ᵉₐ

-- Ty⟦_⟧ₓ : Demand.Ty → Type
-- Ty⟦ Demand.`Bool ⟧ₓ   = Bool
-- Ty⟦ Demand.`T τ ⟧ₓ    = Ty⟦ τ ⟧ₓ
-- Ty⟦ Demand.`List τ ⟧ₓ = List Ty⟦ τ ⟧ₓ

-- reify : ∀ {τ} → Ty⟦ Ty⟦ τ ⟧ₜ ⟧ → Γ ⊢ Ty⟦ τ ⟧ₜ
-- reify {τ = Demand.`Bool} false = `false
-- reify {τ = Demand.`Bool} true = `true
-- reify {τ = Demand.`T τ} (thunk x) = `thunk (reify  x)
-- reify {τ = Demand.`T τ} undefined = `undefined
-- reify {τ = Demand.`List τ} = foldrA (λ xT tT → T.rec (λ x → `thunk (reify x)) `undefined xT `∷ T.rec `thunk `undefined tT) `[]

-- reifyₐ : ∀ {τ} {v : Demand.𝔼⟦ τ ⟧ᵗ} → 𝔻⟦ τ ⟧ᵗ≺ v → Γ ⊢ Ty⟦ τ ⟧ₜ
-- reifyₐ {Γ = Γ} a = reify {Γ = Γ} ⟦ a ⟧ᵉₐ

-- reifyₑ : ∀ {τ} → Demand.𝔼⟦ τ ⟧ᵗ → Γ ⊢ Ty⟦ τ ⟧ₜ
-- reifyₑ {τ = Demand.`Bool} false = `false
-- reifyₑ {τ = Demand.`Bool} true = `true
-- reifyₑ {τ = Demand.`T τ} v = `thunk (reifyₑ v)
-- reifyₑ {τ = Demand.`List τ} v = foldr (λ v′ t → `thunk (reifyₑ v′) `∷ `thunk t) `[] v

reify : ∀ {τ} → Ty⟦ τ ⟧ → Γ ⊢ τ
reify {τ = `Bool} false = `false
reify {τ = `Bool} true = `true
reify {τ = τ₁ `× τ₂} (v₁ , v₂) = reify v₁ `, reify v₂
reify {τ = `T τ} (thunk v₁) = `thunk (reify v₁)
reify {τ = `T τ} undefined = `undefined
reify {τ = `ℕ} v = # v
reify {τ = `ListA τ} v = foldrA (λ v₁ t₂T → T.rec (`thunk ∘ reify) `undefined v₁ `∷ T.rec `thunk `undefined t₂T) `[] v

-- Translate a demand-language value.
𝔼⟦_⟧ᵗ⌊_⌋ : (α : Demand.Ty) → 𝔼⟦ α ⟧ᵗ → Ty⟦ Ty⟦ α ⟧ₜ ⟧
𝔼⟦_⟧ᵗ⌊_⌋ `Bool v = v
𝔼⟦_⟧ᵗ⌊_⌋ (`T α) v = thunk 𝔼⟦ α ⟧ᵗ⌊ v ⌋
𝔼⟦_⟧ᵗ⌊_⌋ (`List α) vs = foldr (λ v vs′ → thunk 𝔼⟦ α ⟧ᵗ⌊ v ⌋ ∷ thunk vs′) [] vs

-- reifyₑ : ∀ {α} → 𝔼⟦ α ⟧ᵗ → Γ ⊢ Ty⟦ α ⟧ₜ
-- reifyₑ v = reify 𝔼⟦ _ ⟧ᵗ⌊ v ⌋

eval-reify : ∀ {α} (v : Ty⟦ α ⟧) → ⟦ reify v ⟧ᵉ g ∋ v
eval-reify {α = `Bool} false = `false
eval-reify {α = `Bool} true = `true
eval-reify {α = α₁ `× α₂} (v₁ , v₂) = eval-reify v₁ `, eval-reify v₂
eval-reify {α = `T α} (thunk v₁) = `thunk (eval-reify v₁)
eval-reify {α = `T α} undefined = `undefined
eval-reify {α = `ℕ} v = # v
eval-reify {α = `ListA α} v = {!!}

-- Translating and then reifying a demand-language
-- eval-reifyₑ : ∀ {α} (v : 𝔼⟦ α ⟧ᵗ) → ⟦ reifyₑ v ⟧ᵉ g ∋ 𝔼⟦ α ⟧ᵗ⌊ v ⌋
-- eval-reifyₑ {α = `Bool} v = {!reify!}
-- eval-reifyₑ {α = `T α} v = {!!}
-- eval-reifyₑ {α = `List α} v = {!!}

-- eval-reifyₐ : ∀ {α} {v : Demand.𝔼⟦ α ⟧ᵗ} (a : 𝔻⟦ α ⟧ᵗ≺ v) {g} →
--   ⟦ reifyₐ {Γ = Γ} a ⟧ᵉ g ∋ ⟦ a ⟧ᵉₐ
-- eval-reifyₐ {α = Demand.`Bool} {false} (𝔻⟦_⟧ᵗ≺_.↓Bool) = `false
-- eval-reifyₐ {α = Demand.`Bool} {true} (𝔻⟦_⟧ᵗ≺_.↓Bool) = `true
-- eval-reifyₐ {α = Demand.`T α} (𝔻⟦_⟧ᵗ≺_.thunk a) = `thunk (eval-reifyₐ a)
-- eval-reifyₐ {α = Demand.`T α} 𝔻⟦_⟧ᵗ≺_.undefined = `undefined
-- eval-reifyₐ {α = Demand.`List α} 𝔻⟦_⟧ᵗ≺_.[] = `[]
-- eval-reifyₐ {α = Demand.`List α} (a 𝔻⟦_⟧ᵗ≺_.∷ a₁) = {!!}

demand₁ : ∀ {Γ α β}
  {g : Demand.𝔼⟦ Γ ⸴ α ⟧ᶜ} →
  (t : Demand.Tm (Γ ⸴ α) β) →
  Demand.𝔻⟦ β ⟧ᵗ≺ Demand.𝔼⟦ t ⟧ᵉ g →
  Tick Ty⟦ Ty⟦ α ⟧ₜ ⟧
demand₁ {g = _ ∷ _} t a = do
  m ⸴ a′ ← Demand.𝔻⟦ t ⟧ᵉ _ a
  return ⟦ a′ ⟧ᵉₐ

demand₂ : ∀ {Γ α β} →
  Demand.Tm (Γ ⸴ α) β →
  Demand.𝔼⟦ α ⟧ᵗ →
  Ctx⟦ Γ ⟧ₜ ⸴ Ty⟦ β ⟧ₜ ⊢ `M Ty⟦ α ⟧ₜ
demand₂ t v =
   let outD = ` sucᵛ (sucᵛ zeroᵛ) in
  `let reify 𝔼⟦ _ ⟧ᵗ⌊ v ⌋ `in
   let a = ` sucᵛ zeroᵛ in
  `let `free `in
   let inD = `fst (` zeroᵛ) in
   let c = `snd (` zeroᵛ) in
  `assert inD `≲ a `in
  `assert ↑ᵗ (subsume1 ⟦ t ⟧ᵉₜ) `≟ (outD `, c) `in
  ` zeroᵛ

-- demand₂-if₁ : ∀ {Γ α β}
--   (t₁ : Demand.Tm (Γ ⸴ α) Demand.`Bool)
--   (t₂ t₃ : Demand.Tm (Γ ⸴ α) β)
--   (v : Demand.𝔼⟦ α ⟧ᵗ)
--   g v′ →
--   ⟦ demand₂ (`if t₁ `then t₂ `else t₃) v ⟧ᵉ g v →


⌊_⌋ᵃ : ∀ {α} {v : Demand.𝔼⟦ α ⟧ᵗ} → Demand.𝔻⟦ α ⟧ᵗ≺ v → Ty⟦ Ty⟦ α ⟧ₜ ⟧
⌊_⌋ᵃ {Demand.`Bool} (𝔻⟦_⟧ᵗ≺_.↓Bool {v = v}) = v
⌊_⌋ᵃ {Demand.`T α} (𝔻⟦_⟧ᵗ≺_.thunk v) = thunk ⌊ v ⌋ᵃ
⌊_⌋ᵃ {Demand.`T α} 𝔻⟦_⟧ᵗ≺_.undefined = undefined
⌊_⌋ᵃ {Demand.`List α} 𝔻⟦_⟧ᵗ≺_.[] = []
⌊_⌋ᵃ {Demand.`List α} (v 𝔻⟦_⟧ᵗ≺_.∷ v₁) = ⌊ v ⌋ᵃ ∷ ⌊ v₁ ⌋ᵃ

Ctx⟦_⟧ₑ : ∀ {Γ} {g : Demand.𝔼⟦ Γ ⟧ᶜ} → Demand.𝔻⟦ Γ ⟧ᶜ≺ g → Ctx⟦ Ctx⟦ Γ ⟧ₜ ⟧
Ctx⟦_⟧ₑ {g = []} [] = []
Ctx⟦_⟧ₑ {g = g ⸴ px} (g′ ⸴ px′) = Ctx⟦_⟧ₑ g′ ⸴ ⌊ px′ ⌋ᵃ

-- theorem₁-∷ : ∀ {Γ α β}
--   (t₁ : Demand.Tm (Γ ⸴ α) (Demand.`T β))
--   (t₂ : Demand.Tm (Γ ⸴ α) (Demand.`T (Demand.`List β)))
--   (g : Demand.𝔼⟦ Γ ⟧ᶜ)
--   (a : Demand.𝔼⟦ α ⟧ᵗ)
--   (outD₁ : 𝔻⟦ Demand.`T β ⟧ᵗ≺ Demand.E⟦ t₁ ⟧ᵉ (g , a))
--   (outD₂ : 𝔻⟦ Demand.`T (Demand.`List β) ⟧ᵗ≺ Demand.E⟦ t₂ ⟧ᵉ (g , a)) →

lemma₁ : ∀ {α} {a : 𝔼⟦ α ⟧ᵗ} (inD : 𝔻⟦ α ⟧ᵗ≺ a) →
  Ty⟦ Ty⟦ α ⟧ₜ ⟧[ ⟦ inD ⟧ᵉₐ ≲ 𝔼⟦ α ⟧ᵗ⌊ a ⌋ ]
lemma₁ {α} {a} ↓Bool = ≲-Bool
lemma₁ {α} {a} (thunk inD) = ≲-thunk (lemma₁ inD)
lemma₁ {α} {a} (undefined) = ≲-undefined
lemma₁ {α} {a} [] = ≲-[]
lemma₁ {α} {a} (inD₁ ∷ inD₂) = ≲-∷ (lemma₁ inD₁) (lemma₁ inD₂)

------------------------------------------------
-- Soundness with respect to demand semantics --
------------------------------------------------

lemma₃ :
  ∀ {Γ α}
    (t : Demand.Tm Γ α)
    {g : 𝔼⟦ Γ ⟧ᶜ}
    {g₁ g₂ : 𝔻⟦ Γ ⟧ᶜ≺ g}
    v
  → g₁ ≤ᶜ g₂
  → ⟦ ⟦ t ⟧ᵉₜ ⟧ᵉ Ctx⟦ g₁ ⟧ₑ ∋ v
  → ⟦ ⟦ t ⟧ᵉₜ ⟧ᵉ Ctx⟦ g₂ ⟧ₑ ∋ v
lemma₃ t v g₁≤g₂ φ = {!!}

-- First major theorem: starting with a certain output demand, evaluating
-- "backwards" in demand semantics and then evaluating "forwards" in logic
-- semantics yields the original output demand at the same cost.
lemma₂ :
  ∀ {Γ α}
    (t : Demand.Tm Γ α)
    (g : 𝔼⟦ Γ ⟧ᶜ)
    (outD : 𝔻⟦ α ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ g) →
    let (inDs , c) = 𝔻⟦ t ⟧ᵉ g outD
    in ⟦ ⟦ t ⟧ᵉₜ ⟧ᵉ Ctx⟦ inDs ⟧ₑ ∋ (⟦ outD ⟧ᵉₐ , c)
lemma₂ (Demand.` x) g outD = {!!}
lemma₂ (Demand.`let t₁ `in t₂) g outD = {!!}
lemma₂ Demand.`false g ↓Bool = `false `, # 0
lemma₂ Demand.`true g ↓Bool = `true `, # 0
lemma₂ (Demand.`if t₁ `then t₂ `else t₃) g outD = {!!}
lemma₂ Demand.`[] g [] = `[] `, # 0
lemma₂ (t₁ Demand.`∷ t₂) g (d₁ ∷ d₂) = `let {!lemma₂ t₁ g d₁!} `in {!!}
lemma₂ (Demand.`foldr t t₁ t₂) g outD = {!!}
lemma₂ (Demand.`tick t) g outD = lemma₂ t g outD
lemma₂ (Demand.`lazy t) g outD = {!!}
lemma₂ (Demand.`force t) g outD = `let (lemma₂ t g (thunk outD)) `in `T-case-thunk (`proj1 (` zeroᵛ)) (` zeroᵛ) `, `proj2 (` zeroᵛ)

sound : ∀ {Γ α β}
  {g : 𝔼⟦ Γ ⟧ᶜ}
  (a : 𝔼⟦ α ⟧ᵗ)
  (t : Demand.Tm (Γ ⸴ α) β)
  (outD : 𝔻⟦ β ⟧ᵗ≺ 𝔼⟦ t ⟧ᵉ (g ⸴ a)) →
  case 𝔻⟦ t ⟧ᵉ (g ⸴ a) outD of λ{
    ((inDs ⸴ inD) , c) → ⟦ demand₂ t a ⟧ᵉ (Ctx⟦ inDs ⟧ₑ ⸴ ⟦ outD ⟧ᵉₐ) ∋ (⟦ inD ⟧ᵉₐ , c)
  }
sound {α = α} {g = g} a t outD with 𝔻⟦ t ⟧ᵉ (g ⸴ a) outD | inspect (𝔻⟦ t ⟧ᵉ (g ⸴ a)) outD
... | ((inDs ⸴ inD) , c) | [ φ ] =
  `let eval-reify 𝔼⟦ α ⟧ᵗ⌊ a ⌋ `in
  `let `free `in
  `if `≲-true (`proj1 (` zeroᵛ)) (` sucᵛ zeroᵛ) (lemma₁ inD) `then
  `if `≟-true (weaken-eval (exchange-eval (weaken-eval {!!}))) (` sucᵛ (sucᵛ zeroᵛ) `, `proj2 (` zeroᵛ)) `then
  (` zeroᵛ)

-----------------------------------------------
-- Adequacy with respect to demand semantics --
-----------------------------------------------

-- theorem₂ : ∀ {Γ α β}
--   (t : Demand.Tm (Γ ⸴ α) β)
--   (g : Demand.𝔼⟦ Γ ⟧ᶜ)
--   (v : Demand.𝔼⟦ α ⟧ᵗ)
--   (outD : Ty⟦ Ty⟦ β ⟧ₜ ⟧)
--   (inD : _) (c : ℕ) →
--   ⟦ demand₂ t v ⟧ᵉ ({!Ctx⟦ g ⟧ₑ!} ⸴ outD) ∋ (inD , c) →
--   runWriter (Demand.𝔻⟦ t ⟧ᵉ {!!} {!!}) ≡ (c , {!!})
-- theorem₂ = {!!}

-- theorem₂ : ∀ {α β}
--   (t : Demand.Tm ([] ⸴ α) β)
--   (g : Demand.𝔼⟦ [] ⟧ᶜ)
--   (v : Demand.𝔼⟦ α ⟧ᵗ)
--   (outD : Demand.𝔻⟦ β ⟧ᵗ≺ Demand.𝔼⟦ t ⟧ᵉ ([] ⸴ v))
--   (inD : _) (c : ℕ) →
--   ⟦ demand₂ t v ⟧ᵉ ([] ⸴ ⌊ outD ⌋ᵃ) ∋ (⌊ inD ⌋ᵃ , c) →
--   Demand.𝔻⟦ t ⟧ᵉ ([] ⸴ v) outD ≡ ([] ⸴ inD , c)
-- theorem₂ (Demand.` x₄) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Demand.`let t `in t₁) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ Demand.`false g v 𝔻⟦_⟧ᵗ≺_.↓Bool inD c (`let x `in (`let `free `in (`if `≲-true (`proj1 (` .zeroᵛ)) (` .(sucᵛ zeroᵛ)) x₅ `then (`if `≟-true (`false `, # .0) (` .(sucᵛ (sucᵛ zeroᵛ)) `, `proj2 (` .zeroᵛ)) `then (` .zeroᵛ))))) = {!!}
-- theorem₂ Demand.`true g v outD inD c (`let x `in (`let `free `in (`if `≲-true x₂ x₄ x₅ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Demand.`if t `then t₁ `else t₂) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ Demand.`[] g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (t Demand.`∷ t₁) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Demand.`foldr t t₁ t₂) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Demand.`tick t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Demand.`lazy t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
-- theorem₂ (Demand.`force t) g v outD inD c (`let x `in (`let `free `in (`if x₂ `then (`if `≟-true x₁ x₃ `then (` .zeroᵛ))))) = {!!}
