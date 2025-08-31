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

module RightInv.Part3.Step6 (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where
  open import RightInv.Base A conA (((X , x) , p) , p⋆ , hypCon , fib-set)
  open import RightInv.Part3.Base A conA (((X , x) , p) , p⋆ , hypCon , fib-set)

  abstract
    step₆ : q ≡ p⋆
    step₆ = transportRefl _ ∙ lem p⋆
      where
        lem : {A : Type} {x y : A} (p : x ≡ y)
          → transport (λ i → x ≡ p i) refl ≡ p
        lem {x = x} = J (λ _ p → transport (λ i → x ≡ p i) refl ≡ p) (transportRefl refl)
