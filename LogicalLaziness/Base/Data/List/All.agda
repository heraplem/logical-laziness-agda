module LogicalLaziness.Base.Data.List.All where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional.Properties

open import LogicalLaziness.Base.Core
open import LogicalLaziness.Base.Data.List.Membership.Propositional

private
  variable
    x : A
    xs ys : List A
    pxs : All P xs
    pys : All P ys

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

map-toList : ∀ {q r}
               {Q : (x : A) → P x → Type q}
               {R : (x : A) → P x → Type r}
           → (∀ {x} {px : P x} → Q x px → R x px)
           → All (uncurry Q) (All.toList pxs)
           → All (uncurry R) (All.toList pxs)
map-toList {pxs = []}       h []           = []
map-toList {pxs = px ∷ pxs} h (qpx ∷ qpxs) = h qpx ∷ map-toList h qpxs

uncurry-const⁻ : ∀ {q} {Q : A → Type q} {xs} {pxs : All.All P xs}
  → All.All (uncurry (λ x _ → Q x)) (All.toList pxs)
  → All.All Q xs
uncurry-const⁻ {pxs = []      } []         = []
uncurry-const⁻ {pxs = px ∷ pxs} (qx ∷ qxs) = qx ∷ uncurry-const⁻ qxs

module _ {f e} (pf : ∀ {x y} → P x → P y → P (f x y)) (pe : P e) where
  foldr⁺ : ∀ {xs}
         → All P xs
         → P (foldr f e xs)
  foldr⁺ []         = pe
  foldr⁺ (px ∷ pxs) = pf px (foldr⁺ pxs)
