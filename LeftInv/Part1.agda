open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Base
open import Paths

module LeftInv.Part1 (A : Pointed ℓ-zero) ((subgroup BG Bi Bi-⋆ isBi isCon grpBG) : SubGroupπ₁ A) where
  open import LeftInv.Base A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)

  abstract
    congP1 : congP (λ i → Bi≡tr∘Bi∘tr i) (transport-filler ⟨BG⟩≡∥X∥ (pt BG)) ≡
      cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹ ∙ transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ (transport ⟨BG⟩≡∥X∥ (pt BG)))) ⁻¹
    congP1 = congP-funTypeTransp Bi (pt BG) ⟨BG⟩≡∥X∥
