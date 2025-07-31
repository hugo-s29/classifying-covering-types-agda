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

module RightInv.Part3.Base (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where
  open import RightInv.Base A conA (((X , x) , p) , p⋆ , hypCon , fib-set)

  q : p x ≡ pt A
  q = transport refl (transport (λ i → p x ≡ p⋆ i) refl)
