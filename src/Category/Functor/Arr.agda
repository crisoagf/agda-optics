module Category.Functor.Arr where
open import Agda.Primitive using (_⊔_)
open import Category.Functor     using (RawFunctor    ; module RawFunctor    )
open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Function using (_∘_)
open import Category.Functor.Lawful
open import Relation.Binary.PropositionalEquality using (refl)

Arr : ∀ {l₁ l₂} → Set l₁ → Set l₂ → Set (l₁ ⊔ l₂)
Arr A B = A → B

arrFunctor : ∀ {l₁ l₂} {B : Set l₁} → RawFunctor (Arr {l₁} {l₂} B)
arrFunctor = record { _<$>_ = λ z z₁ x → z (z₁ x) } -- auto-found

arrLawfulFunctor : ∀ {l₁ l₂} {B : Set l₁} → LawfulFunctorImp (arrFunctor {l₁} {l₂} {B})
arrLawfulFunctor = record
  { <$>-identity = refl
  ; <$>-compose  = refl
  }

arrApplicative : ∀ {l₁} {B : Set l₁} → RawApplicative (Arr {l₁} {l₁} B)
arrApplicative = record { pure = λ z x → z ; _⊛_ = λ z z₁ x → z x (z₁ x) } -- auto-found

arrLawfulApplicative : ∀ {l₁} {B : Set l₁} → LawfulApplicativeImp (arrApplicative {l₁} {B})
arrLawfulApplicative = record
  { ⊛-identity = refl
  ; ⊛-homomorphism = refl
  ; ⊛-interchange = refl
  ; ⊛-composition = refl
  }

