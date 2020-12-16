module Category.Functor.Lawful where
open import Agda.Primitive using (lsuc; _⊔_)
open import Category.Functor
open import Category.Applicative
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning; sym; cong)

record LawfulFunctorImp {l₁ l₂} {F : Set l₁ → Set l₂} (FFunc : RawFunctor F) : Set (lsuc l₁ ⊔ l₂) where
  open RawFunctor FFunc
  field
    <$>-identity : ∀ {a} {x : F a} → (id <$> x) ≡ x
    <$>-compose  : ∀ {a b c} {f : a → b} {g : b → c} {x : F a} → ((g ∘ f) <$> x) ≡ (g <$> (f <$> x))

module LawfulFunctor {l₁ l₂} {F : Set l₁ → Set l₂} {FFunc : RawFunctor F} (FLawful : LawfulFunctorImp FFunc) where
  open RawFunctor FFunc public
  open LawfulFunctorImp FLawful public

record LawfulApplicativeImp {l} {F : Set l → Set l} (FAppl : RawApplicative F) : Set (lsuc l) where
  open RawApplicative FAppl
  field
    ⊛-identity     : ∀ {A}     {u : F A}                                 → (pure id ⊛ u) ≡ u
    ⊛-homomorphism : ∀ {A B}   {u :    A → B } {v : A}                   → (pure u ⊛ pure v) ≡ pure (u v)
    ⊛-interchange  : ∀ {A B}   {u : F (A → B)} {v : A}                   → (u ⊛ pure v) ≡ (pure (λ uᵢ → uᵢ v) ⊛ u)
    ⊛-composition  : ∀ {A B C} {u : F (B → C)} {v : F (A → B)} {w : F A} → (pure (λ f g a → f (g a)) ⊛ u ⊛ v ⊛ w) ≡ (u ⊛ (v ⊛ w))
  open ≡-Reasoning
  private
    composelemma  : ∀ {a b c} {f : a → b} {g : b → c} {x : F a} → ((g ∘ f) <$> x) ≡ (g <$> (f <$> x))
    composelemma {_} {_} {_} {f} {g} {x} =
      pure (λ x₁ → g (f x₁)) ⊛ x ≡⟨ cong (_⊛ x) (sym ⊛-homomorphism) ⟩
      pure (λ f x → g (f x)) ⊛ pure f ⊛ x ≡⟨ cong ((_⊛ x) ∘ (_⊛ pure f)) (sym ⊛-homomorphism) ⟩
      pure (λ g f x → g (f x)) ⊛ pure g ⊛ pure f ⊛ x ≡⟨ ⊛-composition ⟩
      pure g ⊛ (pure f ⊛ x) ∎
  isLawfulFunctor : LawfulFunctorImp rawFunctor
  isLawfulFunctor = record
    { <$>-identity = ⊛-identity
    ; <$>-compose = composelemma
    }

module LawfulApplicative {l} {F : Set l → Set l} (FAppl : RawApplicative F) (FLawful : LawfulApplicativeImp FAppl) where
  open RawApplicative FAppl public
  open LawfulApplicativeImp FLawful public
  open LawfulFunctorImp isLawfulFunctor public
