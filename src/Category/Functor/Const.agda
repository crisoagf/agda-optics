module Category.Functor.Const where
open import Category.Functor     using (RawFunctor    ; module RawFunctor    )
open import Category.Functor.Lawful
open import Relation.Binary.PropositionalEquality using (refl)

Const : ∀ {l₁ l₂} (R : Set l₂) (_ : Set l₁) → Set l₂ 
Const R _ = R

constFunctor : ∀ {l₁} {R : Set l₁} → RawFunctor (Const {l₁} R)
constFunctor = record { _<$>_ = λ _ z → z }

constLawfulFunctor : ∀ {l₁} {R : Set l₁} → LawfulFunctorImp (constFunctor {l₁} {R})
constLawfulFunctor = record { <$>-identity = refl ; <$>-compose = refl }

