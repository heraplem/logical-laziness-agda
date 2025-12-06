module LogicalLaziness.Base.Data.List.All where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Data.List
  as List
import Data.List.Properties as List
open import Data.List.Relation.Unary.All
  as All
open import Data.List.Relation.Unary.All.Properties
  as All
open import Data.List.Relation.Unary.Any
import Data.List.Relation.Unary.Any.Properties
  as Any
open import Data.List.Membership.Propositional.Properties

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.Data.List.Membership.Propositional

private
  variable
    x : A
    xs ys zs : List A
    pxs : All P xs
    pys : All P ys
    pzs : All P zs

∈ᴸ⇒lookup∈ᴸtoList : (x∈xs : x ∈ᴸ xs)
                  → (x , All.lookup pxs x∈xs) ∈ᴸ All.toList pxs
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (here refl)  = here refl
∈ᴸ⇒lookup∈ᴸtoList {pxs = _ ∷ _} (there x∈xs) = there (∈ᴸ⇒lookup∈ᴸtoList x∈xs)

-- This complicated-looking lemma shows how to expand an application of the form
-- `h (lookup pxs x∈xs)`.
app-lookup : ∀ {q} {Q : B → Type q}
               {x : A} {xs : List A} (x∈xs : x ∈ᴸ xs)
               (pxs : All P xs)
               (f : A → B)
               (h : {x : A} → P x → Q (f x))
           → h (All.lookup pxs x∈xs) ≡ All.lookup {P = Q} (All.gmap⁺ h pxs) (∈ᴸ⇒∈ᴸ-map f x∈xs)
app-lookup (here refl ) (px ∷ pxs) f h = refl
app-lookup (there x∈xs) (px ∷ pxs) f h = app-lookup x∈xs pxs f h

lookup-++ˡ : {xs ys : List A} {pxs : All P xs} {pys : All P ys} {x : A} (x∈xs : x ∈ᴸ xs)
           → All.lookup (All.++⁺ pxs pys) (∈-++⁺ˡ x∈xs) ≡ All.lookup pxs x∈xs
lookup-++ˡ {pxs = _ ∷ _   } (here _)     = refl
lookup-++ˡ {pxs = px ∷ pxs} (there x∈xs) = lookup-++ˡ {pxs = pxs} x∈xs

lookup-++ʳ : {pxs : All P xs} {pys : All P ys} (x∈ys : x ∈ᴸ ys)
           → All.lookup (All.++⁺ pxs pys) (∈-++⁺ʳ xs x∈ys) ≡ All.lookup pys x∈ys
lookup-++ʳ {pxs = []      } x∈ys = refl
lookup-++ʳ {pxs = px ∷ pxs} x∈ys = lookup-++ʳ {pxs = pxs} x∈ys

lookup-∈-++⁻ : ∀ {v} (pxs : All P xs) (pys : All P ys)
                 (v∈[xs++ys] : v ∈ᴸ xs ++ ys)
               → All.lookup (++⁺ pxs pys) v∈[xs++ys] ≡ (case ∈-++⁻ xs v∈[xs++ys] of λ
                   { (inj₁ x∈xs) → All.lookup pxs x∈xs
                   ; (inj₂ x∈ys) → All.lookup pys x∈ys
                   })
lookup-∈-++⁻               []         pys v∈ys               = refl
lookup-∈-++⁻               (px ∷ pxs) pys (here refl)        = refl
lookup-∈-++⁻ {xs = x ∷ xs} (px ∷ pxs) pys (there v∈[xs++ys])
 with Any.++⁻ xs v∈[xs++ys] | lookup-∈-++⁻ pxs pys v∈[xs++ys]
... | inj₁ v∈xs             | ψ = ψ
... | inj₂ v∈ys             | ψ = ψ

map⁺-map⁻ : ∀ {a b p q}
              {A : Type a} {B : Type b}
              {P : B → Type p} {Q : A → Type q}
              {f : A → B}
              (g₁ : ∀ {x} → P (f x) → Q x)
              (g₂ : ∀ {x} → Q x → P (f x))
          → (∀ {x} pfx → g₂ {x} (g₁ pfx) ≡ pfx)
          → {xs : List A} (pxs : All P (List.map f xs))
          → All.map⁺ (All.map g₂ (All.map g₁ (All.map⁻ pxs))) ≡ pxs
map⁺-map⁻ g₁ g₂ η {[]    } []         = refl
map⁺-map⁻ g₁ g₂ η {x ∷ xs} (px ∷ pxs) = cong₂ _∷_ (η px) (map⁺-map⁻ g₁ g₂ η pxs)

subst-∷ : (px : P x) (pxs : All P xs) (pys : All P ys)
          (ψ : xs ≡ ys)
        → subst (All P) ψ pxs ≡ pys
        → subst (All P) (cong (x ∷_) ψ) (px ∷ pxs) ≡ px ∷ pys
subst-∷ _ _ _ refl refl = refl

subst-++-assoc : (pxs : All P xs) (pys : All P ys) (pzs : All P zs)
               → subst (All P) (List.++-assoc xs ys zs) (++⁺ (++⁺ pxs pys) pzs) ≡ (++⁺ pxs (++⁺ pys pzs))
subst-++-assoc                                   []         _   _   = refl
subst-++-assoc {xs = x ∷ xs} {ys = ys} {zs = zs} (px ∷ pxs) pys pzs =
  subst-∷
    px
    (++⁺ (++⁺ pxs pys) pzs)
    (++⁺ pxs (++⁺ pys pzs))
    (List.++-assoc xs ys zs)
    (subst-++-assoc pxs pys pzs)

map-toList : ∀ {q r}
               {Q : (x : A) → P x → Type q}
               {R : (x : A) → P x → Type r}
           → (∀ {x} {px : P x} → Q x px → R x px)
           → All (uncurry Q) (All.toList pxs)
           → All (uncurry R) (All.toList pxs)
map-toList {pxs = []}       h []           = []
map-toList {pxs = px ∷ pxs} h (qpx ∷ qpxs) = h qpx ∷ map-toList h qpxs

toList⁻ : ∀ {q} {Q : A → Type q} {xs} {pxs : All P xs}
  → All (uncurry (λ x _ → Q x)) (All.toList pxs)
  → All Q xs
toList⁻ {pxs = []      } []         = []
toList⁻ {pxs = px ∷ pxs} (qx ∷ qxs) = qx ∷ toList⁻ qxs

module _ {f e} (pf : ∀ {x y} → P x → P y → P (f x y)) (pe : P e) where
  foldr⁺ : ∀ {xs}
         → All P xs
         → P (foldr f e xs)
  foldr⁺ []         = pe
  foldr⁺ (px ∷ pxs) = pf px (foldr⁺ pxs)
