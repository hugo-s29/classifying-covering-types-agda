open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim ; map2 to ∥-∥ₕ-map2 ; elim2 to ∥-∥ₕ-elim2)
open import Base
open import Paths

module RightInv.Part2-Lemma.Step2 (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) (x : ⟨ X∙ ⟩) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part2-Lemma.Base A (covering X∙ p p⋆ fib-set isCon) x

  abstract
    lem-cong∙ : {A B : Type} (h : A → B) {a b c d e f : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e) (t : e ≡ f) →
        cong h (p ∙ q ∙ r ∙ s ∙ t) ≡ cong h p ∙ cong h q ∙ cong h r ∙ cong h s ∙ cong h t
    lem-cong∙ h p q r s t =
        cong h (p ∙ q ∙ r ∙ s ∙ t)
        ≡⟨ cong∙ h p (q ∙ r ∙ s ∙ t) ⟩
        cong h p ∙ cong h (q ∙ r ∙ s ∙ t)
        ≡⟨ cong (λ u → cong h p ∙ u) (cong∙ h q (r ∙ s ∙ t)) ⟩
        cong h p ∙ cong h q ∙ cong h (r ∙ s ∙ t)
        ≡⟨ cong (λ u → cong h p ∙ cong h q ∙ u) (cong∙ h r (s ∙ t)) ⟩
        cong h p ∙ cong h q ∙ cong h r ∙ cong h (s ∙ t)
        ≡⟨ cong (λ u → cong h p ∙ cong h q ∙ cong h r ∙ u) (cong∙ h s t) ⟩
        cong h p ∙ cong h q ∙ cong h r ∙ cong h s ∙ cong h t ∎

    step₂ : subst (λ q → e (e' (∣ x ∣ , a , q)) ≡ (∣ x ∣ , a , q) ) (transport⁻Transport (PathIdTrunc 2) refl) (cong fst (
        cong {B = λ _ → fiber p̃ a}
          (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                  (λ q → x , q ∙ refl) u .fst) ,
                      ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                      (λ q → x , q ∙ refl) u .snd) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
        ∙ cong {B = λ _ → fiber p̃ a} ( e x ,_ ) (rUnit q) ⁻¹
        ∙ cong₃ {A = ⟨ A ⟩} {B = λ a → ∥p∥ ∣ x ∣ ≡ ∣ a ∣} {C = λ a' _ → a' ≡ a} {D = λ _ _ _ → fiber p̃ a}
              (λ u v w → (∣ x ∣ , u , v) , w) q (λ i j → ∣ q (i ∧ j) ∣) (λ i j → q (i ∨ j))
        ∙ cong {A = ∣ p x ∣ ≡ ∣ a ∣} {B = λ _ → fiber p̃ a }
              (λ u → (∣ x ∣ , a , u) , refl) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹
        ∙ refl
      )) ≡ subst (λ q → e (e' (∣ x ∣ , a , q)) ≡ (∣ x ∣ , a , q) ) (transport⁻Transport (PathIdTrunc 2) refl)
        (cong fst (cong {B = λ _ → fiber p̃ a}
          (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                  (λ q → x , q ∙ refl) u .fst) ,
                      ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                      (λ q → x , q ∙ refl) u .snd) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣))
        ∙ cong fst (cong {B = λ _ → fiber p̃ a} ( e x ,_ ) (rUnit q)) ⁻¹
        ∙ cong fst (cong₃ {A = ⟨ A ⟩} {B = λ a → ∥p∥ ∣ x ∣ ≡ ∣ a ∣} {C = λ a' _ → a' ≡ a} {D = λ _ _ _ → fiber p̃ a}
              (λ u v w → (∣ x ∣ , u , v) , w) q (λ i j → ∣ q (i ∧ j) ∣) (λ i j → q (i ∨ j)))
        ∙ cong fst (cong {A = ∣ p x ∣ ≡ ∣ a ∣} {B = λ _ → fiber p̃ a }
              (λ u → (∣ x ∣ , a , u) , refl) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣)) ⁻¹
        ∙ refl
      )
    step₂ = cong (subst (λ q → e (e' (∣ x ∣ , a , q)) ≡ (∣ x ∣ , a , q) ) (transport⁻Transport (PathIdTrunc 2) refl)) (lem-cong∙ fst
      (cong {B = λ _ → fiber p̃ a} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst) , ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .snd) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣))
      (cong {B = λ _ → fiber p̃ a} ( e x ,_ ) (rUnit q) ⁻¹)
      (cong₃ {A = ⟨ A ⟩} {B = λ a → ∥p∥ ∣ x ∣ ≡ ∣ a ∣} {C = λ a' _ → a' ≡ a} {D = λ _ _ _ → fiber p̃ a} (λ u v w → (∣ x ∣ , u , v) , w) q (λ i j → ∣ q (i ∧ j) ∣) (λ i j → q (i ∨ j)))
      (cong {A = ∣ p x ∣ ≡ ∣ a ∣} {B = λ _ → fiber p̃ a } (λ u → (∣ x ∣ , a , u) , refl) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹)
      refl)
