module Category.Choice where
open import Data.Sum using (_⊎_)
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Category.Profunctor

record ChoiceImp {a b : Level} (p : Set a → Set a → Set b) : Set (lsuc (a ⊔ b)) where
  field
    isProfunctor : ProfunctorImp p
    left' : ∀ {x y z : Set a} → p x y → p (x ⊎ z) (y ⊎ z)
    right' : ∀ {x y z : Set a} → p x y → p (z ⊎ x) (z ⊎ y)

module Choice {a b : Level} {p : Set a → Set a → Set b} (isChoice : ChoiceImp p) where
  left : ∀ {x y z : Set a} → p x y → p (x ⊎ z) (y ⊎ z)
  left = ChoiceImp.left' isChoice
  right : ∀ {x y z : Set a} → p x y → p (z ⊎ x) (z ⊎ y)
  right = ChoiceImp.right' isChoice
  open Profunctor (ChoiceImp.isProfunctor isChoice)

