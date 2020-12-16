module Optics.Lens where
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Function.Inverse using (_↔_; inverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; module ≡-Reasoning; cong)

open import Category.Functor.Arr
open import Category.Functor.Const
open import Category.Profunctor.Star
open import Category.Strong
open import Optics

Lens : ∀ {l} (S T A B : Set l) → Set (lsuc l)
Lens = Optic StrongImp

module Lens {l} {S T A B : Set l} (lens : Lens S T A B) where
  get : S → A
  get = getOptic S T A B (starStrong constFunctor) lens
  set : S → B → T
  set = setOptic S T A B (starStrong arrFunctor) lens

record LawfulLens {l} {S A : Set l} (lens' : Lens S S A A) : Set (lsuc l) where
  open Lens lens' public
  lens : Lens S S A A
  lens = lens'
  field
    setget : ∀ (s : S) → set s (get s) ≡ s
    getset : ∀ (s : S) (a : A) → get (set s a) ≡ a
    setset : ∀ (s : S) (a a' : A) → set (set s a) ≡ set s


lensIso : ∀ {l} {S A : Set l} {lens : Lens S S A A} → (lawful : LawfulLens lens) → S ↔ (∃[ a ] ∃[ c ] ∃[ s ] (c ≡ Lens.set lens s × Lens.get lens s ≡ a))
lensIso {_} {S} {A} lawful = inverse to from from∘to to∘from
   where
     open LawfulLens lawful
     to : S → ∃[ a ] ∃[ c ] ∃[ s ] (c ≡ set s × get s ≡ a)
     to s = get s , set s , s , refl , refl
     from : ∃[ a ] ∃[ c ] ∃[ s ] (c ≡ set s × get s ≡ a) → S
     from (a , c , _ , _  , _) = c a
     from∘to : (s : S) → from (to s) ≡ s
     from∘to = setget
     to∘from : (elem : ∃[ a ] ∃[ c ] ∃[ s ] (c ≡ set s × get s ≡ a)) → to (from elem) ≡ elem
     open ≡-Reasoning
     to∘from (.(get s) , .(set s) , s , refl , refl) = begin
       (get (set s (get s)) , set (set s (get s)) , set s (get s) , _ , _) ≡⟨ cong (λ sᵢ → get sᵢ , set sᵢ , sᵢ , refl , refl) (setget s) ⟩
       (get s , set s , s , _ , _) ∎

