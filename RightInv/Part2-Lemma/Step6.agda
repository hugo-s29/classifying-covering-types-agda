open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim ; map2 to ∥-∥ₕ-map2 ; elim2 to ∥-∥ₕ-elim2)
open import Base

module RightInv.Part2-Lemma.Step6 (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x') , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) (x : X) where
  open import RightInv.Base A conA (((X , x') , p) , p⋆ , hypCon , fib-set)
  open import RightInv.Part2-Lemma.Base A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x

  abstract
    step₆ : cong (λ q → e(e' (∣ x ∣ , a , q))) (transport⁻Transport (PathIdTrunc 2) refl) ⁻¹
      ∙ cong {B = λ _ → X̃} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣)
      ∙ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transport⁻Transport (PathIdTrunc 2) refl) ⁻¹
      ∙ cong {B = λ _ → X̃} (λ q → ∣ x ∣ , a , q)  (transport⁻Transport (PathIdTrunc 2) refl)
      ≡ cong (λ q → e(∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q ∙ refl) (transport (PathIdTrunc 2) q) .fst)) (transport⁻Transport (PathIdTrunc {A = ⟨ A ⟩} {a = p x} 2) refl) ⁻¹
      ∙ cong (λ u → e (∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣)
    step₆ = cong (λ u →
          cong (λ q → e(e' (∣ x ∣ , a , q))) (transport⁻Transport (PathIdTrunc 2) refl) ⁻¹
        ∙ cong {B = λ _ → X̃} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣)
        ∙ u
      ) (lCancel (cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transport⁻Transport (PathIdTrunc 2) refl)))
      ∙ cong (λ u → cong (λ q → e(e' (∣ x ∣ , a , q))) (transport⁻Transport (PathIdTrunc 2) refl) ⁻¹ ∙ u) (rUnit (cong {B = λ _ → X̃} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣))) ⁻¹
