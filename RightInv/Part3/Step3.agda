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
open import Base
open import Paths
open import UniversalCovering

module RightInv.Part3.Step3 (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part3.Base A (covering X∙ p p⋆ fib-set isCon)

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

    step₃ :
        cong (λ q → p (e' (∣ x ∣ , pt A , q))) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹
        ∙ cong (p̃ ∘ fst) (e∘e'-mini-lemma x (pt A) (cong ∣_∣ p⋆))
        ≡ cong (λ q → p (e' (∣ x ∣ , pt A , q))) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹
        ∙ cong (λ u → p̃ (e (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst) ))
          (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
        ∙ refl
        ∙ q
        ∙ refl
        ∙ refl
    step₃ = cong (cong (λ q → p (e' (∣ x ∣ , pt A , q))) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹ ∙_)
        (lem-cong∙ (p̃ ∘ fst)
            (cong {B = λ _ → fiber p̃ (pt A)} (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst) , ∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .snd) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣))
            (cong {B = λ _ → fiber p̃ (pt A)} ( e x ,_ ) (rUnit q) ⁻¹)
            (cong₃ {A = ⟨ A ⟩} {B = λ a → ∥p∥ ∣ x ∣ ≡ ∣ a ∣} {C = λ a' _ → a' ≡ (pt A)} {D = λ _ _ _ → fiber p̃ (pt A)} (λ u v w → (∣ x ∣ , u , v) , w) q (λ i j → ∣ q (i ∧ j) ∣) (λ i j → q (i ∨ j)))
            (cong {A = ∣ p x ∣ ≡ ∣ pt A ∣} {B = λ _ → fiber p̃ (pt A) } (λ u → (∣ x ∣ , pt A , u) , refl) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹)
            refl
        )
