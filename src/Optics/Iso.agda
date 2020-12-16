module Optics.Iso where
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Function.Equality using (Π)
open import Function.Inverse using (_↔_; inverse; Inverse; _InverseOf_)
open import Relation.Binary.PropositionalEquality using (_≡_; →-to-⟶; refl)

open import Category.Functor.Arr
open import Category.Functor.Const
open import Category.Profunctor
open import Category.Profunctor.Star
open import Category.Profunctor.Joker
open import Optics

Iso : ∀ {l} (S T A B : Set l) → Set (lsuc l)
Iso = Optic ProfunctorImp

module Iso {l} {S T A B : Set l} (iso : Iso S T A B) where
  get : S → A
  get = getOptic S T A B (starProfunctor constFunctor) iso
  put : B → T
  put = putOptic S T A B (jokerProfunctor arrFunctor) iso

record LawfulIsoImp {l} {S A : Set l} (iso' : Iso S S A A) : Set (lsuc l) where
  open Iso iso'
  field
    putget : ∀ (s : S) → put (get s) ≡ s
    getput : ∀ (a : A) → get (put a) ≡ a

module LawfulIso {l} {S A : Set l} {iso' : Iso S S A A} (isLawful : LawfulIsoImp iso') where
  open Iso iso' public
  iso : Iso S S A A
  iso = iso'
  open LawfulIsoImp isLawful public

isoIso : ∀ {S A : Set} {iso : Iso S S A A} → (i : LawfulIsoImp iso) → S ↔ A
isoIso {S} {A} i = inverse to from from∘to to∘from
  where
    open LawfulIso i
    to = get
    from = put
    from∘to : (s : S) → from (to s) ≡ s
    from∘to = putget
    to∘from : (a : A) → to (from a) ≡ a
    to∘from = getput

invLawfulIso : ∀ {l} {S A : Set l} {get : S → A} {put : A → S} → (→-to-⟶ get) InverseOf (→-to-⟶ put) ↔ LawfulIsoImp (λ p → Profunctor.dimap p get put)
invLawfulIso = inverse invertibleIsLawful lawfulIsInvertible (λ _ → refl) (λ _ → refl)
  where
    invertibleIsLawful : ∀ {l} {S A : Set l} {get : S → A} {put : A → S} → (→-to-⟶ get) InverseOf (→-to-⟶ put) → LawfulIsoImp (λ p → Profunctor.dimap p get put)
    invertibleIsLawful i = record
      { putget = right-inverse-of
      ; getput = left-inverse-of
      } where
        open _InverseOf_ i
    
    lawfulIsInvertible : ∀ {l} {S A : Set l} {get : S → A} {put : A → S} → LawfulIsoImp (λ p → Profunctor.dimap p get put) → (→-to-⟶ get) InverseOf (→-to-⟶ put)
    lawfulIsInvertible isLawful = record
      { left-inverse-of = getput
      ; right-inverse-of = putget
      }
      where open LawfulIso isLawful

