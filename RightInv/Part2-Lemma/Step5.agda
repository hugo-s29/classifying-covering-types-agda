open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim ; map2 to ∥-∥ₕ-map2 ; elim2 to ∥-∥ₕ-elim2)
open import Base

module RightInv.Part2-Lemma.Step5 (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) (x : ⟨ X∙ ⟩) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part2-Lemma.Base A (covering X∙ p p⋆ fib-set isCon) x

  abstract
    step₅ : subst (λ q → e (e' (∣ x ∣ , a , q)) ≡ (∣ x ∣ , a , q)) (transport⁻Transport (PathIdTrunc 2) refl)
        (cong {B = λ _ → X̃} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                  (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣)
        ∙ refl
        ∙ refl
        ∙ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transport⁻Transport (PathIdTrunc 2) refl) ⁻¹
        ∙ refl
      ) ≡ subst (λ q → e (e' (∣ x ∣ , a , q)) ≡ (∣ x ∣ , a , q)) (transport⁻Transport (PathIdTrunc 2) refl)
        (cong {B = λ _ → X̃} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                  (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣)
        ∙ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transport⁻Transport (PathIdTrunc 2) refl) ⁻¹)
    step₅ = cong (subst (λ q → e (e' (∣ x ∣ , a , q)) ≡ (∣ x ∣ , a , q)) (transport⁻Transport (PathIdTrunc 2) refl))
      (cong (cong {B = λ _ → X̃} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                  (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣) ∙_) (rUnit _ ∙ lUnit _ ∙ lUnit _) ⁻¹)
