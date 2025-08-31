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

module RightInv.Part3.Step5 (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where
  open import RightInv.Base A conA (((X , x) , p) , p⋆ , hypCon , fib-set)
  open import RightInv.Part3.Base A conA (((X , x) , p) , p⋆ , hypCon , fib-set)

  abstract
    step₅ : cong (λ q → p (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) (transport (PathIdTrunc 2) q) .fst)) (transport⁻Transport (PathIdTrunc 2) (cong ∣_∣ p⋆)) ⁻¹
        ∙ cong (λ u → p (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
        ∙ q
        ≡ q
    step₅ = cong (λ u → u ⁻¹ ∙ cong (λ u → p (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ∙ q)
      (tr∘tr∘tr (PathIdTrunc 2) (λ q → p(∥-∥ₕ-elim (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) q .fst)) (cong ∣_∣ p⋆))
      ∙ assoc _ _ _
      ∙ cong (_∙ q) (lCancel (cong (λ u → p (∥-∥ₕ-elim {B = λ _ → fiber p (pt A)} (λ _ → fib-set (pt A)) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)))
      ∙ lUnit q ⁻¹
