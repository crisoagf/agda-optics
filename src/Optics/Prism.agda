module Optics.Prism where
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; fromInj₂)
open import Data.Empty using (⊥-elim)
open import Function.Inverse using (_↔_; inverse)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; module ≡-Reasoning; cong; cong₂; sym)

open import Category.Functor.Arr
open import Category.Functor.Either
open import Category.Profunctor.Star
open import Category.Profunctor.Joker
open import Category.Choice
open import Optics

Prism : ∀ {l} (S T A B : Set l) → Set (lsuc l)
Prism = Optic ChoiceImp

module Prism {l} {S T A B : Set l} (prism : Prism S T A B) where
  matching : S → A ⊎ T
  matching = matchingOptic S T A B (starChoice eitherApplicative) prism
  put : B → T
  put = putOptic S T A B (jokerChoice arrFunctor) prism

record LawfulPrism {l} {S A : Set l} (prism' : Prism S S A A) : Set (lsuc l) where
  open Prism prism' public
  prism : Prism S S A A
  prism = prism'
  field
    matchingput : ∀ (a : A) → matching (put a) ≡ inj₁ a
    putmatching : ∀ (s : S) (a : A) → matching s ≡ inj₁ a → put a ≡ s
    matchingmatching : ∀ (s t : S) → matching s ≡ inj₂ t → matching t ≡ inj₂ s

  matchingWithWitness : (s : S) → (Σ[ a ∈ A ] matching s ≡ inj₁ a) ⊎ (Σ[ t ∈ S ] matching s ≡ inj₂ t)
  matchingWithWitness s with matching s
  ...                      | inj₁ a = inj₁ (a , refl)
  ...                      | inj₂ t = inj₂ (t , refl)

uninjed₁ : ∀ {l₁ l₂} {A : Set l₁} {B : Set l₂} {x x₁ : A} → inj₁ {l₁} {l₂} {A} {B} x ≡ inj₁ {l₁} {l₂} {A} {B} x₁ → x ≡ x₁
uninjed₁ refl = refl

uninjed₂ : ∀ {l₁ l₂} {A : Set l₁} {B : Set l₂} {x x₁ : B} → inj₂ {l₁} {l₂} {A} {B} x ≡ inj₂ {l₁} {l₂} {A} {B} x₁ → x ≡ x₁
uninjed₂ refl = refl

inj₁≢inj₂ : ∀ {l₁ l₂} {A : Set l₁} {B : Set l₂} {x : A} {x₁ : B} → inj₁ x ≢ inj₂ x₁
inj₁≢inj₂ ()

prismIso : ∀ {l} {S A : Set l} {prism : Prism S S A A} → (lawful : LawfulPrism prism) → S ↔ (A ⊎ ∃[ s ] ∃[ t ] (Prism.matching prism s ≡ inj₂ t))
prismIso {_} {S} {A} lawful = inverse to from from∘to to∘from
   where
     open LawfulPrism lawful
     to : S → A ⊎ ∃[ s ] ∃[ t ] (matching s ≡ inj₂ t)
     to s with matchingWithWitness s
     ...     | inj₁ (a , _)          = inj₁ a
     ...     | inj₂ (t , w)          = inj₂ (s , t , w)
     from : A ⊎ ∃[ s ] ∃[ t ] (matching s ≡ inj₂ t) → S
     from (inj₁ x) = put x
     from (inj₂ (s , t , matchs≡injt)) = s
     from∘to : (s : S) → from (to s) ≡ s
     from∘to s with matchingWithWitness s
     ...          | inj₁ (a , w) = putmatching s a w
     ...          | inj₂ (t , _) = refl
     congΣ : ∀ {l₁ l₂} {T : Set l₁} {cmp : Set l₂} (W : T → cmp) (x : cmp) (t t' : T) (w : x ≡ W t) (w' : x ≡ W t') → t ≡ t' → (t , w) ≡ (t' , w')
     congΣ _ _ _ _ refl refl refl = refl
     to∘from : (elem : A ⊎ ∃[ s ] ∃[ t ] (matching s ≡ inj₂ t)) → to (from elem) ≡ elem
     open ≡-Reasoning
     to∘from (inj₁ x) with matchingWithWitness (put x)
     ...                 | inj₁ ( x₁ , w ) = cong inj₁ (uninjed₁ (inj₁ x₁ ≡⟨ sym w ⟩ matching (put x) ≡⟨ matchingput x ⟩ inj₁ x ∎))
     ...                 | inj₂ ( x₁ , w ) = ⊥-elim (inj₁≢inj₂ (inj₁ x ≡⟨ sym (matchingput x) ⟩ matching (put x) ≡⟨ w ⟩ inj₂ x₁ ∎))
     to∘from (inj₂ (s , t , w)) with matchingWithWitness s
     ...                           | inj₂ (t₁ , w₁) = cong inj₂ (cong (s ,_) (congΣ (λ tᵢ → inj₂ tᵢ) (matching s) t₁ t w₁ w (uninjed₂ (inj₂ t₁ ≡⟨ sym w₁ ⟩ matching s ≡⟨ w ⟩ inj₂ t ∎))))
     ...                           | inj₁ (a  , w₁) = ⊥-elim (inj₁≢inj₂ (inj₁ a ≡⟨ sym w₁ ⟩ matching s ≡⟨ w ⟩ inj₂ t ∎))

