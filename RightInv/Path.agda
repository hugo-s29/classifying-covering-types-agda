open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim ; map2 to ∥-∥ₕ-map2 ; elim2 to ∥-∥ₕ-elim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-∥-rec ; map to ∥-∥-map ; map2 to ∥-∥-map2 ; elim to ∥-∥-elim ; elim2 to ∥-∥-elim2 ; elim3 to ∥-∥-elim3)
open import Cubical.Homotopy.Connected
open import Cubical.WildCat.Base
open import Base
open import Pullback
open import Paths
open import UniversalCovering

module RightInv.Path (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Decompose A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part1 A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part2 A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part3 A (covering X∙ p p⋆ fib-set isCon)

  abstract
    p⋆-result : congP (λ i → p̃≡p i) x≡x̃ ≡ p⋆ ⁻¹
    p⋆-result =
          congP (λ i → p̃≡p i) x≡x̃
      ≡⟨ congP-subst-rUnit X̃≡X p̃≡p∙ x≡x̃∙ ⟩
          congP (λ i → p̃≡p∙ i) x≡x̃∙
      ≡⟨ decompose ⟩
          compPathP'
          {p = X̃≡X}
          {q = refl}
          (congP (λ i → p̃≡tr∘p̃∘tr i) x̃≡tr-x̃)
          (congP (λ i → tr∘p̃∘tr≡p̃∘e i) tr-x̃≡e'x̃)
      ≡⟨ compPathP'-nondep {r = X̃≡X} {s = refl} (congP (λ i → p̃≡tr∘p̃∘tr i) x̃≡tr-x̃) (congP (λ i → tr∘p̃∘tr≡p̃∘e i) tr-x̃≡e'x̃) ⟩
          congP (λ i → p̃≡tr∘p̃∘tr i) x̃≡tr-x̃
          ∙ congP (λ i → tr∘p̃∘tr≡p̃∘e i) tr-x̃≡e'x̃
      ≡⟨ cong₂ _∙_ congP1 congP2 ⟩
         (cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙ transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃))) ⁻¹)
         ∙ (transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃))) ∙ cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹)
      ≡⟨ assoc _ _ _ ⁻¹ ⟩
         cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙ transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃))) ⁻¹
         ∙ transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃))) ∙ cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹
      ≡⟨ cong (cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙_) (assoc _ _ _) ⟩
         cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙ (transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃))) ⁻¹
         ∙ transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃)))) ∙ cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹
      ≡⟨ cong (λ u → cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙ u ∙ cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹) (lCancel (transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃))))) ⟩
         cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙ refl ∙ cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹
      ≡⟨ cong (cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙_) (lUnit (cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹)) ⁻¹ ⟩
         cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙ cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹
      ≡⟨ assoc _ _ _ ⟩
         (cong p̃ (transport⁻Transport X̃≡X x̃) ⁻¹ ∙ cong p̃ (transport⁻Transport X̃≡X x̃)) ∙ cong p̃ (e∘e' x̃) ⁻¹
      ≡⟨ cong (_∙ cong p̃ (e∘e' x̃) ⁻¹) (lCancel (cong p̃ (transport⁻Transport X̃≡X x̃))) ⟩
         refl ∙ cong p̃ (e∘e' x̃) ⁻¹
      ≡⟨ lUnit _ ⁻¹ ⟩
         cong p̃ (e∘e' x̃) ⁻¹
      ≡⟨ cong sym congP3 ⟩
        p⋆ ⁻¹ ∎
