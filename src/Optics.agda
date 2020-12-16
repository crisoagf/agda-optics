module Optics where
open import Agda.Primitive using (_⊔_; lsuc)
open import Data.Maybe using (Maybe; just)
open import Data.Sum using (_⊎_; inj₁)
open import Function using (const; id)
open import Category.Functor.Arr
open import Category.Functor.Const
open import Category.Functor.Either
open import Category.Profunctor.Joker
open import Category.Profunctor.Star

Optic : ∀ {l p} (c : (Set l → Set l → Set l) → Set p) (s t a b : Set l) → Set (lsuc l ⊔ p)
Optic {l} c s t a b = ∀ {p : Set l → Set l → Set l} (isClass : c p) → p a b → p s t

setOptic : ∀ {l p} (S T A B : Set l) {c : (Set l → Set l → Set l) → Set p} (isClass : c (Star (Arr B))) → Optic c S T A B → S → B → T
setOptic _ _ _ _ isClass l = l isClass (const id)

putOptic : ∀ {l p} (S T A B : Set l) {c : (Set l → Set l → Set l) → Set p} (isClass : c (Joker (Arr B))) → Optic c S T A B → B → T
putOptic _ _ _ _ isClass l = l isClass id

getOptic : ∀ {l p} (S T A B : Set l) {c : (Set l → Set l → Set l) → Set p} (isClass : c (Star (Const A))) → Optic c S T A B → S → A
getOptic _ _ _ _ isClass l = l isClass id

matchingOptic : ∀ {l p} (S T A B : Set l) {c : (Set l → Set l → Set l) → Set p} (isClass : c (Star (Either A))) → Optic c S T A B → S → A ⊎ T
matchingOptic _ _ _ _ isClass l = l isClass inj₁

previewOptic : ∀ {l p} (S T A B : Set l) {c : (Set l → Set l → Set l) → Set p} (isClass : c (Star (Const (Maybe A)))) → Optic c S T A B → S → Maybe A
previewOptic _ _ _ _ isClass l = l isClass just

