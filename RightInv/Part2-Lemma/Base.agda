open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Base

module RightInv.Part2-Lemma.Base (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) (x : ⟨ X∙ ⟩) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)

  a : ⟨ A ⟩
  a = p x

  q : p x ≡ p x
  q = transport refl (transport refl refl)
