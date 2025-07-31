open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Base

module RightInv.Part2-Lemma.Base (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x') , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) (x : X) where
  open import RightInv.Base A conA (((X , x') , p) , p⋆ , hypCon , fib-set)

  a : ⟨ A ⟩
  a = p x

  q : p x ≡ p x
  q = transport refl (transport refl refl)
