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

module LeftInv.Decompose1 (A : Pointed ℓ-zero) ((subgroup BG Bi Bi-⋆ isBi isCon grpBG) : SubGroupπ₁ A) where
  open import LeftInv.Base A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)

  abstract
    decompose₁ : congP (λ i →
            compPathP'
            {A = Type} {B = λ X → X → ∥ ⟨ A ⟩ ∥ 3}
            {x' = Bi}
            {y' = Bi ∘ s}
            {z' = ∥p∥}
            {p = ⟨BG⟩≡∥X∥}
            {q = refl}
            Bi≡Bi∘s
            Bi∘s≡∥p∥ i
        ) (
            compPathP' {A = Type} {B = λ X → X}
                {x' = pt BG}
                {y' = ∣x∣'}
                {z' = ∣x∣}
                {p = ⟨BG⟩≡∥X∥} {q = refl}
                ptBG≡∣x∣'
                ∣x∣'≡∣x∣
        )
        ≡ compPathP'
            {p = ⟨BG⟩≡∥X∥}
            {q = refl}
            (congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣')
            (congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣)
    decompose₁ = congP-compPathP' {B = λ X → X} _ _ ⟨BG⟩≡∥X∥ _ _ ptBG≡∣x∣' _ refl _ ∣x∣'≡∣x∣ _ _ _ Bi≡Bi∘s Bi∘s≡∥p∥
