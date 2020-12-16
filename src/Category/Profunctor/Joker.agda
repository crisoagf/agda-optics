module Category.Profunctor.Joker where
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Category.Functor using (RawFunctor; module RawFunctor)
open import Category.Functor.Lawful
open import Category.Profunctor
open import Category.Choice
open import Relation.Binary.PropositionalEquality using (refl)

Joker : ∀ {l₁ l₂ l₃} (F : Set l₂ → Set l₃) (A : Set l₁) (B : Set l₂) → Set l₃
Joker F _ B = F B

jokerProfunctor : ∀ {l₁ l₂} {F : Set l₁ → Set l₂} → RawFunctor F → ProfunctorImp (Joker F)
jokerProfunctor f = record
  { dimap = λ _ h g → h <$> g
  ; lmap  = λ _ g → g
  ; rmap  = λ h g → h <$> g
  } where open RawFunctor f

jokerLawfulProfunctor : ∀ {l₁ l₂} {F : Set l₁ → Set l₂} {FFunc : RawFunctor F} → LawfulFunctorImp FFunc → LawfulProfunctorImp (jokerProfunctor FFunc)
jokerLawfulProfunctor f = record
  { lmapId = refl
  ; rmapId = <$>-identity
  ; dimapLmapRmap = refl
  } where open LawfulFunctor f

jokerChoice : ∀ {l₁ l₂} {F : Set l₁ → Set l₂} → RawFunctor F → ChoiceImp (Joker F)
jokerChoice f  = record
  { isProfunctor = jokerProfunctor f
  ; left' = inj₁ <$>_ 
  ; right' = inj₂ <$>_
  }
  where open RawFunctor f

