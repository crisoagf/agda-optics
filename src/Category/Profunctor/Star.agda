module Category.Profunctor.Star where
open import Agda.Primitive using (_⊔_)
open import Category.Functor     using (RawFunctor    ; module RawFunctor)
open import Category.Functor.Lawful
open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Category.Profunctor
open import Category.Strong
open import Category.Choice
open import Relation.Binary.PropositionalEquality using (refl)
open import Axiom.Extensionality.Propositional using (Extensionality)

Star : ∀ {l₁ l₂ l₃} (F : Set l₂ → Set l₃) (A : Set l₁) (B : Set l₂) → Set (l₁ ⊔ l₃)
Star F A B = (A → F B)

starProfunctor : ∀ {l₁ l₂} {F : Set l₁ → Set l₂} → RawFunctor F → ProfunctorImp (Star F)
starProfunctor f = record
  { dimap = λ f h g z → h <$> (g (f z))
  ; lmap  = λ f g z → g (f z)
  ; rmap  = λ h g z → h <$> (g z)
  } where open RawFunctor f

starLawfulProfunctor : ∀ {l₁ l₂} {F : Set l₁ → Set l₂} {Func : RawFunctor F} → Extensionality l₁ l₂ → LawfulFunctorImp Func → LawfulProfunctorImp (starProfunctor Func) 
starLawfulProfunctor ext f = record
  { lmapId = refl
  ; rmapId = ext (λ _ → <$>-identity)
  ; dimapLmapRmap = refl
  } where open LawfulFunctor f

starStrong : ∀ {l₁ l₂} {F : Set l₁ → Set l₂} → RawFunctor F → StrongImp (Star F)
starStrong f = record
  { first'  = λ { f → λ { (x , z) → (_, z) <$> f x } }
  ; second' = λ { f → λ { (z , x) → (z ,_) <$> f x } }
  ; isProfunctor = starProfunctor f
  } where open RawFunctor f

starChoice : ∀ {l} {F : Set l → Set l} → RawApplicative F → ChoiceImp (Star F)
starChoice f = record
  { left'  = λ { f → λ { (inj₁ x) → inj₁ <$> f x ; (inj₂ z) → pure (inj₂ z) } }
  ; right' = λ { f → λ { (inj₁ z) → pure (inj₁ z) ; (inj₂ x) → inj₂ <$> f x } }
  ; isProfunctor = starProfunctor rawFunctor
  } where open RawApplicative f

