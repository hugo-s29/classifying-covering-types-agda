open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.HITs.Truncation
open import Base
open import Pullback
open import Paths

module RightInv.Decompose (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)

  abstract
    decompose : congP (λ i →
            compPathP'
            {A = Type} {B = λ X → X → ⟨ A ⟩}
            {x' = p̃}
            {y' = transport refl ∘ p̃ ∘ transport⁻ X̃≡X}
            {z' = p̃ ∘ e}
            {p = X̃≡X}
            {q = refl}
            p̃≡tr∘p̃∘tr
            tr∘p̃∘tr≡p̃∘e i
        ) (
            compPathP' {A = Type} {B = λ X → X}
                {x' = x̃}
                {y' = transport X̃≡X x̃}
                {z' = pt X∙}
                {p = X̃≡X} {q = refl}
                x̃≡tr-x̃
                tr-x̃≡e'x̃
        )
        ≡ compPathP'
            {p = X̃≡X}
            {q = refl}
            (congP (λ i → p̃≡tr∘p̃∘tr i) x̃≡tr-x̃)
            (congP (λ i → tr∘p̃∘tr≡p̃∘e i) tr-x̃≡e'x̃)
    decompose = congP-compPathP' {B = λ X → X} _ _ X̃≡X _ _ x̃≡tr-x̃ _ refl _ tr-x̃≡e'x̃ _ _ _ p̃≡tr∘p̃∘tr tr∘p̃∘tr≡p̃∘e
