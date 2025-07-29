module Logic where

open import Agda.Builtin.FromNat
open import Function
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Bool
  as Bool
  hiding (T)
open import Data.Product
  as Σ
open import Data.Product.Properties
  as Σ
open import Data.Nat
  as ℕ
open import Data.List
  as List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional

open import Core
open import Explicit
  using (ty⟦_⟧ₐ≺_)

infixr 5 _`×_
data ty : Type where
  `Bool  : ty
  _`×_   : ty → ty → ty
  `T     : ty → ty
  `ℕ     : ty
  `ListA : ty → ty

variable
  α β τ : ty

ctx : Type
ctx = List ty

variable
  Γ Δ : ctx

infix  1.59  `_ #_
infixl 1.56  _`+_
infixr 1.55  _`∷_
infixr 1.54  _`,_
infix  1.54  _`≟_ _`≲_
infixr 1.51  _`?_ _`>>=_
infix  1.505 `if_`then_`else_ `assert_`in_
infix  1.50  `let_`in_

infix 4 _⊢_
data _⊢_ : ctx → ty → Type where

  `_               : τ ∈ Γ → Γ ⊢ τ

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
  Number-tm : ∀ {Γ} → Number (Γ ⊢ `ℕ)
  Number-tm = record
    { Constraint = const ⊤
    ; fromNat    = λ n → # n
    }

ty⟦_⟧ : ty → Type
ty⟦ `Bool    ⟧ = Bool
ty⟦ α `× β   ⟧ = ty⟦ α ⟧ × ty⟦ β ⟧
ty⟦ `T α     ⟧ = T ty⟦ α ⟧
ty⟦ `ℕ       ⟧ = ℕ
ty⟦ `ListA α ⟧ = ListA ty⟦ α ⟧

ty-≡-dec : DecidableEquality ty⟦ τ ⟧
ty-≡-dec {`Bool}    = Bool._≟_
ty-≡-dec {α `× β}   = Σ.≡-dec ty-≡-dec ty-≡-dec
ty-≡-dec {`T τ}     = T-≡-dec ty-≡-dec
ty-≡-dec {`ℕ}       = ℕ._≟_
ty-≡-dec {`ListA τ} = ListA-≡-dec ty-≡-dec

ctx⟦_⟧ : ctx → Type
ctx⟦_⟧ = All ty⟦_⟧

variable
  g γ : ctx⟦ Γ ⟧

---------------
-- Renamings --
---------------

Ren : ctx → ctx → Type
Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ

variable
  ρ : Ren Γ Δ

↑ʳ_ : Ren Γ Δ → Ren (Γ ⸴ τ) (Δ ⸴ τ)
↑ʳ_ ρ zvar     = zvar
↑ʳ_ ρ (svar x) = svar (ρ x)

infixr -1 _$ʳ_
_$ʳ_ : Ren Γ Δ → Γ ⊢ τ → Δ ⊢ τ
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
↑ᵗ_ = (svar $ʳ_)

-------------------
-- Substitutions --
-------------------

Sub : ctx → ctx → Type
Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Δ ⊢ τ

↑ˢ_ : Sub Γ Δ → Sub (Γ ⸴ τ) (Δ ⸴ τ)
(↑ˢ σ) zvar     = ` zvar
(↑ˢ σ) (svar x) = ↑ᵗ σ x

infixr -1 _$ˢ_
_$ˢ_ : Sub Γ Δ → Γ ⊢ τ → Δ ⊢ τ
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

----------------
-- Evaluation --
----------------

data foldrA⟦_,_,_⟧_∋_
    (P_∋_ : ctx⟦ Γ ⸴ `T α ⸴ β ⟧ → ty⟦ β ⟧ → Type)
    (e : ty⟦ β ⟧) :
    T (ListA ty⟦ α ⟧) →
    ctx⟦ Γ ⟧ →
    ty⟦ β ⟧ →
    Type where
  foldrA-undefined : foldrA⟦ P , e , undefined ⟧ g ∋ e
  foldrA-[]        : foldrA⟦ P , e , thunk []  ⟧ g ∋ e
  foldrA-∷         : ∀ {b b′ a as} →
    foldrA⟦ P , e , as ⟧ g ∋ b →
    P (g ⸴ a ⸴ b) ∋ b′ →
    foldrA⟦ f , e , thunk (a ∷ as) ⟧ g ∋ b′

data tm⟦_⟧ : ∀ {Γ τ} → Γ ⊢ τ → ctx⟦ Γ ⟧ → ty⟦ τ ⟧ → Type where
  `_                : (x : τ ∈ Γ) → tm⟦ ` x ⟧ g (All.lookup g x)
  `let_`in_         : ∀ {v₁ v₂} → tm⟦ t₁ ⟧ g v₁ → tm⟦ t₂ ⟧ (g ⸴ v₁) v₂ → tm⟦ `let t₁ `in t₂ ⟧ g v₂
  `false            : tm⟦ `false ⟧ g false
  `true             : tm⟦ `false ⟧ g true
  _`≟_              : {v₁ v₂ : ty⟦ τ ⟧} → tm⟦ t₁ ⟧ g v₁ → tm⟦ t₂ ⟧ g v₂ → tm⟦ t₁ `≟ t₂ ⟧ g ⌊ ty-≡-dec v₁ v₂ ⌋
  _`,_              : ∀ {v₁ v₂} → tm⟦ t₁ ⟧ g v₁ → tm⟦ t₂ ⟧ g v₂ → tm⟦ t₁ `, t₂ ⟧ g (v₁ , v₂)
  `fst              : ∀ {v} → tm⟦ t ⟧ g v → tm⟦ `fst t ⟧ g (proj₁ v)
  `snd              : ∀ {v} → tm⟦ t ⟧ g v → tm⟦ `snd t ⟧ g (proj₂ v)
  `T-case-undefined : ∀ {v} →
    tm⟦ t₁ ⟧ g undefined →
    tm⟦ t₃ ⟧ g v →
    tm⟦ `T-case t₁ t₂ t₃ ⟧ g v
  `T-case-thunk     : ∀ {v₁ v₂} →
    tm⟦ t₁ ⟧ g (thunk v₁) →
    tm⟦ t₂ ⟧ (g ⸴ v₁) v₂ →
    tm⟦ `T-case t₁ t₂ t₃ ⟧ g v₂
  #_                : ∀ n → tm⟦ # n ⟧ g n
  _`+_              : ∀ {n₁ n₂} → tm⟦ t₁ ⟧ g n₁ → tm⟦ t₂ ⟧ g n₂ → tm⟦ t₁ `+ t₂ ⟧ g (n₁ + n₂)
  `[]               : ∀ {τ} → tm⟦_⟧ {τ = `ListA τ} `[] g []
  _`∷_              : ∀ {x xs} → tm⟦ t₁ ⟧ g x → tm⟦ t₂ ⟧ g xs → tm⟦ t₁ `∷ t₂ ⟧ g (x ∷ xs)
  `foldrA           : ∀ {e xs b} →
    tm⟦ t₂ ⟧ g e →
    tm⟦ t₃ ⟧ g xs →
    foldrA⟦ tm⟦ t₁ ⟧ , e , thunk xs ⟧ g ∋ b →
    tm⟦ `foldrA t₁ t₂ t₃ ⟧ g b
  `free             : ∀ {v : ty⟦ α ⟧} → tm⟦ `free ⟧ g v
  ?l                : ∀ {x} → tm⟦ t₁ ⟧ g x → tm⟦ t₁ `? t₂ ⟧ g x
  ?r                : ∀ {x} → tm⟦ t₂ ⟧ g x → tm⟦ t₁ `? t₂ ⟧ g x

postulate
  weaken1 : ∀ {Γ τ α} → Γ ⊢ τ → Γ ⸴ α ⊢ τ
  subsume1 : ∀ {Γ a b x} → Γ ⸴ a ⊢ b → Γ ⸴ x ⸴ a ⊢ b
  weaken2 : ∀ {Γ τ α β} → Γ ⊢ τ → Γ ⸴ α ⸴ β ⊢ τ
  subsume2 : ∀ {Γ a b x y} → Γ ⸴ a ⊢ b → Γ ⸴ x ⸴ y ⸴ a ⊢ b

-----------------
-- Translation --
-----------------

ty⟦_⟧ₜ : Explicit.ty → ty
ty⟦ Explicit.`Bool   ⟧ₜ = `Bool
ty⟦ Explicit.`T τ    ⟧ₜ = `T ty⟦ τ ⟧ₜ
ty⟦ Explicit.`List τ ⟧ₜ = `ListA ty⟦ τ ⟧ₜ

ctx⟦_⟧ₜ : Explicit.ctx → ctx
ctx⟦ γ ⟧ₜ = List.map ty⟦_⟧ₜ γ

`assert_`in_ : Γ ⊢ `Bool → Γ ⊢ τ → Γ ⊢ τ
`assert t₁ `in t₂ = `if t₁ `then t₂ `else `fail

`force : Γ ⊢ `T τ → Γ ⊢ τ
`force t = `T-case t (` zvar) `fail

`M : ty → ty
`M τ = τ `× `ℕ

`return : Γ ⊢ τ → Γ ⊢ `M τ
`return t = t `, 0

`fmap : (Γ ⊢ α → Γ ⊢ β) → Γ ⊢ `M α → Γ ⊢ `M β
`fmap f t = `let t `in `free

_`>>=_ : Γ ⊢ `M α → Γ ⸴ α ⊢ `M β → Γ ⊢ `M β
t₁ `>>= t₂ =
  `let t₁ `in `free
  -- `let t₁ `in
  -- `let (`let `fst (` zvar) `in subsume1 t₂) `in
  -- (`fst (` zvar) `, (`snd (` (there (here refl))) `+ `snd (` (here refl))))

tm⟦_⟧ₜ : ∀ {Γ τ} → Explicit.tm Γ τ → ctx⟦ Γ ⟧ₜ ⊢ `M ty⟦ τ ⟧ₜ
tm⟦ Explicit.` x ⟧ₜ                      = `return (` (∈⇒∈-map ty⟦_⟧ₜ x))
tm⟦ Explicit.`let t₁ `in t₂ ⟧ₜ           = tm⟦ t₁ ⟧ₜ `>>= tm⟦ t₂ ⟧ₜ
tm⟦ Explicit.`false ⟧ₜ                   = `return `false
tm⟦ Explicit.`true ⟧ₜ                    = `return `true
tm⟦ Explicit.`if t₁ `then t₂ `else t₃ ⟧ₜ =
  tm⟦ t₁ ⟧ₜ `>>=
  (`if ` (here refl) `then ↑ᵗ tm⟦ t₂ ⟧ₜ `else ↑ᵗ tm⟦ t₃ ⟧ₜ)
tm⟦ Explicit.`[] ⟧ₜ                      = `return `[]
tm⟦ t₁ Explicit.`∷ t₂ ⟧ₜ                 =
  tm⟦ t₁ ⟧ₜ `>>=
  weaken1 (tm⟦ t₂ ⟧ₜ) `>>=
  `return (` (there (here refl)) `∷ ` (here refl))
tm⟦ Explicit.`foldr t₁ t₂ t₃ ⟧ₜ          = tm⟦ t₂ ⟧ₜ
tm⟦ Explicit.`tick t₁ ⟧ₜ                 = tm⟦ t₁ ⟧ₜ
tm⟦ Explicit.`lazy t₁ ⟧ₜ                 = `fmap `thunk tm⟦ t₁ ⟧ₜ
tm⟦ Explicit.`force t₁ ⟧ₜ                = `fmap `force tm⟦ t₁ ⟧ₜ

tm⟦_⟧ₐ : ∀ {τ v} → ty⟦ τ ⟧ₐ≺ v → ty⟦ ty⟦ τ ⟧ₜ ⟧
tm⟦_⟧ₐ {Explicit.`Bool} (ty⟦_⟧ₐ≺_.↓Bool {v}) = v
tm⟦_⟧ₐ {Explicit.`T τ} (ty⟦_⟧ₐ≺_.↓thunk v) = thunk tm⟦ v ⟧ₐ 
tm⟦_⟧ₐ {Explicit.`T τ} ty⟦_⟧ₐ≺_.↓undefined = undefined
tm⟦_⟧ₐ {Explicit.`List τ} ty⟦_⟧ₐ≺_.↓[] = []
tm⟦_⟧ₐ {Explicit.`List τ} (v ty⟦_⟧ₐ≺_.↓∷ v₁) = tm⟦ v ⟧ₐ ∷ tm⟦ v₁ ⟧ₐ

-- ty⟦_⟧ₓ : Explicit.ty → Type
-- ty⟦ Explicit.`Bool ⟧ₓ   = Bool
-- ty⟦ Explicit.`T τ ⟧ₓ    = ty⟦ τ ⟧ₓ
-- ty⟦ Explicit.`List τ ⟧ₓ = List ty⟦ τ ⟧ₓ

reify : ∀ {τ} → ty⟦ ty⟦ τ ⟧ₜ ⟧ → Γ ⊢ ty⟦ τ ⟧ₜ
reify {τ = Explicit.`Bool} false = `false
reify {τ = Explicit.`Bool} true = `true
reify {τ = Explicit.`T τ} (thunk x) = `thunk (reify  x)
reify {τ = Explicit.`T τ} undefined = `undefined
reify {τ = Explicit.`List τ} [] = `[]
reify {τ = Explicit.`List τ} (x ∷ xs) = reify x `∷ reify xs

reifyₐ : ∀ {τ} {v : Explicit.ty⟦ τ ⟧ₑ} → ty⟦ τ ⟧ₐ≺ v → Γ ⊢ ty⟦ τ ⟧ₜ
reifyₐ a = reify tm⟦ a ⟧ₐ

-- demand : ∀ {Γ α β}
--   {g : Explicit.ctx⟦ Γ ⸴ α ⟧ₑ} →
--   (t : Explicit.tm (Γ ⸴ α) β) →
--   Explicit.ty⟦ β ⟧ₐ≺ Explicit.tm⟦ t ⟧ₑ g →
--   Explicit.M ty⟦ ty⟦ α ⟧ₜ ⟧
-- demand {g = _ ∷ _} t a = do
--   m ⸴ a′ ← Explicit.↓tm t a
--   return tm⟦ a′ ⟧ₐ

demand′ : ∀ {Γ α β}
  {v : Explicit.ty⟦ α ⟧ₑ} →
  Explicit.tm (Γ ⸴ α) β →
  ty⟦ α ⟧ₐ≺ v →
  ctx⟦ Γ ⟧ₜ ⸴ ty⟦ β ⟧ₜ ⊢ `M ty⟦ α ⟧ₜ
demand′ t a =
  let outD = ` svar (svar zvar)
      inD = `fst (` (here refl))
      c = `snd (` (here refl))
  in `let reifyₐ a `in
      let a = ` svar zvar in
     `let `free `in
     `assert inD `≲ a `in
     `assert weaken1 (subsume1 tm⟦ t ⟧ₜ) `≟ (outD `, c) `in
     ` zvar

-- ↓tm : ∀ {Γ} {g : ctx⟦ Γ ⟧ₑ} {τ : ty}
--   (t : Γ ⊢ τ) →
--   ty⟦ τ ⟧ₐ≺ tm⟦ t ⟧ₑ g
--   → M (↓ctx g)


-- g : evaluation context
-- outD

-- demand′ t inV ⇓[ g , outD ] (inD, c)
-- →
-- let ((_ , inD′), c′) = ↓tm {g = g , inV} t outD
-- in (inD , c) ≡ (inD′ , c′)

-- let ((_ , inD′), c′) = ↓tm {g = g , inV} t outD
-- in demand′ t inV ⇓[ g , outD ] (inD , c)

-- the-theorem : ∀ {Γ α β}
--   {v : Explicit.ty⟦ α ⟧ₑ}
--   {g : Explicit.ctx⟦ Γ ⸴ α ⟧ₑ} →
--   (t : Explicit.tm (Γ ⸴ α) β) →
--   (a :
--   tm⟦ demand′ t
