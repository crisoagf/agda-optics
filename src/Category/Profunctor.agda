module Category.Profunctor where
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Product using (_,_; _×_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_)

Dimap : ∀ {a b} (p : Set a → Set a → Set b) → Set (lsuc a ⊔ b)
Lmap : ∀ {a b} (p : Set a → Set a → Set b) → Set (lsuc a ⊔ b)
Rmap : ∀ {a b} (p : Set a → Set a → Set b) → Set (lsuc a ⊔ b)

Dimap p = ∀ {x y z w} → (f : x -> y) -> (h : z -> w) -> (g : p y z) → p x w
Lmap  p = ∀ {x y   w} → (f : x -> y) ->                 (g : p y w) → p x w
Rmap  p = ∀ {x z   w} →                 (h : z -> w) -> (g : p x z) → p x w

record ProfunctorImp {a b : Level} (p : Set a → Set a → Set b) : Set (lsuc (a ⊔ b)) where
  field
    dimap : Dimap p
    lmap  : Lmap  p
    rmap  : Rmap  p

dimapFromLmapRmap : ∀ {a b} {p : Set a → Set a → Set b} (lmap : Lmap p) (rmap : Rmap p) → Dimap p
dimapFromLmapRmap lmap rmap f h g = rmap h (lmap f g)

lmapRmapFromDimap : ∀ {a b} {p : Set a → Set a → Set b} (dimap : Dimap p) → (Lmap p × Rmap p)
lmapRmapFromDimap dimap = (λ f → dimap f id) , dimap id

module Profunctor {a b : Level} {p : Set a → Set a → Set b} (isProfunctor : ProfunctorImp p) where
  open ProfunctorImp isProfunctor public

record LawfulProfunctorImp {a b} {p : Set a → Set a → Set b} (isProfunctor : ProfunctorImp p) : Set (lsuc (a ⊔ b)) where
  open Profunctor isProfunctor
  field
    lmapId : ∀ {a b} {g : p a b} → lmap id g ≡ g
    rmapId : ∀ {a b} {g : p a b} → rmap id g ≡ g
    dimapLmapRmap : ∀ {a b c d} {f : a → b} {g : p b c} {h : c → d} → dimap f h g ≡ lmap f (rmap h g)

module LawfulProfunctor {a b} {p : Set a → Set a → Set b} {isProfunctor : ProfunctorImp p} (isLawful : LawfulProfunctorImp isProfunctor) where
  open Profunctor isProfunctor public
  open LawfulProfunctorImp isLawful public

