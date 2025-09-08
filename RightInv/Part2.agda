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

module RightInv.Part2 (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part2-Lemma A (covering X∙ p p⋆ fib-set isCon)

  abstract
    retEq≡e∘e' : (x̃ : X̃) → retEq X̃≃X x̃ ≡ e∘e' x̃
    retEq≡e∘e' = retEq≡linv e' e e'∘e e∘e' (λ x → lemma x ⁻¹)

    congP2 : congP (λ i → tr∘p̃∘tr≡p̃∘e i) tr-x̃≡e'x̃ ≡ transportRefl (p̃ (transport⁻ X̃≡X (transport X̃≡X x̃))) ∙ cong p̃ (transport⁻Transport X̃≡X x̃) ∙ cong p̃ (e∘e' x̃) ⁻¹
    congP2 =
        congP (λ i → tr∘p̃∘tr≡p̃∘e i) (uaβ X̃≃X x̃)
      ≡⟨ cong (congP (λ i → tr∘p̃∘tr≡p̃∘e i)) (lUnit (uaβ X̃≃X x̃)) ⟩
        congP (λ i x → (transportRefl ( p̃ (transport⁻ X̃≡X x)) ∙ cong p̃ (~uaβ X̃≃X x)) i) (refl ∙ uaβ X̃≃X x̃)
      ≡⟨ congP∙ (λ i x → transportRefl ( p̃ (transport⁻ X̃≡X x)) i) (λ i x → cong p̃ (~uaβ X̃≃X x) i) refl (uaβ X̃≃X x̃) ⟩
        congP (λ i x → transportRefl ( p̃ (transport⁻ X̃≡X x)) i) (refl {x = transport (ua X̃≃X) x̃})
        ∙ congP (λ i x → cong p̃ (~uaβ X̃≃X x) i) (uaβ X̃≃X x̃)
      ≡⟨⟩
        transportRefl ( p̃ (transport⁻ X̃≡X (transport (ua X̃≃X) x̃)))
        ∙ cong p̃ (congP (λ i x → ~uaβ X̃≃X x i) (uaβ X̃≃X x̃))
      ≡⟨ cong (λ u → transportRefl ( p̃ (transport⁻ X̃≡X (transport (ua X̃≃X) x̃))) ∙ cong p̃ u) (ua-tr⁻Tr X̃≃X x̃) ⟩
        transportRefl ( p̃ (transport⁻ (ua X̃≃X) (transport (ua X̃≃X) x̃)))
        ∙ cong p̃ (transport⁻Transport (ua X̃≃X) x̃ ∙ retEq X̃≃X x̃ ⁻¹)
      ≡⟨ cong (λ u → transportRefl ( p̃ (transport⁻ (ua X̃≃X) (transport (ua X̃≃X) x̃))) ∙ cong p̃ (transport⁻Transport (ua X̃≃X) x̃ ∙ u ⁻¹)) (retEq≡e∘e' x̃) ⟩
        transportRefl ( p̃ (transport⁻ (ua X̃≃X) (transport (ua X̃≃X) x̃)))
        ∙ cong p̃ (transport⁻Transport (ua X̃≃X) x̃ ∙ e∘e' x̃ ⁻¹)
      ≡⟨ cong (transportRefl ( p̃ (transport⁻ (ua X̃≃X) (transport (ua X̃≃X) x̃))) ∙_) (cong∙ p̃ (transport⁻Transport (ua X̃≃X) x̃) (e∘e' x̃ ⁻¹)) ⟩
        transportRefl ( p̃ (transport⁻ (ua X̃≃X) (transport (ua X̃≃X) x̃)))
        ∙ cong p̃ (transport⁻Transport (ua X̃≃X) x̃)
        ∙ cong p̃ (e∘e' x̃) ⁻¹ ∎
