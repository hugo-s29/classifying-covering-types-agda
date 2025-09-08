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

module RightInv.Part3.Step4 (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part3.Base A (covering X∙ p p⋆ fib-set isCon)

  abstract
    step₄ : cong (λ q → p (e' (∣ x ∣ , pt A , q))) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹
        ∙ cong (λ u → p̃ (e (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst) )) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
        ∙ refl
        ∙ q
        ∙ refl
        ∙ refl
        ≡ cong (λ q → p (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) (transport (PathIdTrunc 2) q) .fst)) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹
        ∙ cong (λ u → p (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
        ∙ q
    step₄ = cong
             (λ u →
                cong (λ q₁ → p (e' (∣ x ∣ , pt A , q₁))) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹
              ∙ cong (λ u → p̃ (e (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst) )) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
              ∙ u)
             (rUnit _ ∙ cong (q ∙_) (rUnit _) ∙ lUnit _) ⁻¹
