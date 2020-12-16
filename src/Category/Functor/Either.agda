module Category.Functor.Either where
open import Agda.Primitive using (_⊔_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Category.Functor     using (RawFunctor    ; module RawFunctor    )
open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Function using (_∘_)

Either : ∀ {l₁ l₂} (A : Set l₁) (B : Set l₂) → Set (l₁ ⊔ l₂)
Either = _⊎_

eitherFunctor : ∀ {l₁ l₂} {A : Set l₁} → RawFunctor (Either {l₁} {l₂} A)
eitherFunctor = record
  { _<$>_ = λ f → λ { (inj₁ z) → inj₁ z ; (inj₂ a) → inj₂ (f a) }
  }

eitherApplicative : ∀ {l₁} {A : Set l₁} → RawApplicative (Either {l₁} {l₁} A)
eitherApplicative = record
  { pure = inj₂
  ; _⊛_ = λ { (inj₁ a) → λ _ → inj₁ a ; (inj₂ f) → λ { (inj₁ a) → inj₁ a ; (inj₂ b) → inj₂ (f b) } }
  }

