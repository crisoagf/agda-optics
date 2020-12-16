module Category.Strong where
open import Data.Product using (_×_)
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Category.Profunctor

record StrongImp {a b : Level} (p : Set a → Set a → Set b) : Set (lsuc (a ⊔ b)) where
  field
    isProfunctor : ProfunctorImp p
    first' : ∀ {x y z : Set a} → p x y → p (x × z) (y × z)
    second' : ∀ {x y z : Set a} → p x y → p (z × x) (z × y)

module Strong {a b : Level} {p : Set a → Set a → Set b} (isStrong : StrongImp p) where
  first : ∀ {x y z : Set a} → p x y → p (x × z) (y × z)
  first = StrongImp.first' isStrong
  second : ∀ {x y z : Set a} → p x y → p (z × x) (z × y)
  second = StrongImp.second' isStrong
  open Profunctor (StrongImp.isProfunctor isStrong)

