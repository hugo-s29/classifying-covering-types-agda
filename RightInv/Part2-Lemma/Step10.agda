open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim ; map2 to ∥-∥ₕ-map2 ; elim2 to ∥-∥ₕ-elim2)
open import Base

module RightInv.Part2-Lemma.Step10 (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x') , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) (x : X) where
  open import RightInv.Base A conA (((X , x') , p) , p⋆ , hypCon , fib-set)
  open import RightInv.Part2-Lemma.Base A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x

  abstract
    step₁₀ : cong (λ q → e(∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q ∙ refl) q .fst)) (transportTransport⁻ (PathIdTrunc {A = ⟨ A ⟩} 2) (transport (PathIdTrunc 2) refl)) ⁻¹
      ∙ cong (λ u → e (∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) (transport (PathIdTrunc 2) refl))
      ≡ refl
    step₁₀ = lCancel _
