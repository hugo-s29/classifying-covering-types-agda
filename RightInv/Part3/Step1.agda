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
open import UniversalCovering

module RightInv.Part3.Step1 (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part3.Base A (covering X∙ p p⋆ fib-set isCon)

  abstract
    step₁ : cong (p̃ ∘ fst) (
        subst (λ q → Path (fiber p̃ (pt A)) (e (e' (∣ x ∣ , pt A , q)) , e'-fib (pt A) ((∣ x ∣ , pt A , q) , refl) .snd) ((∣ x ∣ , pt A , q) , refl))
        (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) (e∘e'-mini-lemma x (pt A) (cong ∣_∣ p⋆)))
        ≡ cong (p̃ ∘ fst) (
        cong {B = λ _ → fiber p̃ (pt A)} (λ q → e (e' (∣ x ∣ , pt A , q)) , e'-fib (pt A) ((∣ x ∣ , pt A , q) , refl) .snd) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹
        ∙ e∘e'-mini-lemma x (pt A) (cong ∣_∣ p⋆)
        ∙ cong {B = λ _ → fiber p̃ (pt A)} (λ q → ((∣ x ∣ , pt A , q) , refl)) (transport⁻Transport (PathIdTrunc {b = pt A} 2) (cong ∣_∣ p⋆)))
    step₁ = cong (cong (p̃ ∘ fst)) (
        substInPaths
        (λ q → (e (e' (∣ x ∣ , pt A , q)) , e'-fib (pt A) ((∣ x ∣ , pt A , q) , refl) .snd))
        (λ q → ((∣ x ∣ , pt A , q) , refl)) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) (e∘e'-mini-lemma x (pt A) (cong ∣_∣ p⋆)))
