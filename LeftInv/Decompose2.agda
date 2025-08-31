open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
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
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-∥-rec ; map to ∥-∥-map ; map2 to ∥-∥-map2 ; elim to ∥-∥-elim ; elim2 to ∥-∥-elim2 ; elim3 to ∥-∥-elim3)
open import Cubical.Homotopy.Connected
open import Cubical.WildCat.Base
open import Base
open import Pullback
open import Paths
open import UniversalCovering

module LeftInv.Decompose2 (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) (((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib) : SubGroupπ₁' A) where
  open import LeftInv.Base A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)

  abstract
    decompose₂ : congP (λ i → compPathP' {A = Type} {B = λ X → X → ∥ ⟨ A ⟩ ∥ 3} {x' = Bi}
                               {y' = transport refl ∘ Bi ∘ transport⁻ ⟨BG⟩≡∥X∥} {z' = Bi ∘ s}
                               {p = ⟨BG⟩≡∥X∥} {q = refl} Bi≡tr∘Bi∘tr tr∘Bi∘tr≡Bi∘s i)
                       (compPathP' {A = Type} {B = λ X → X} {x' = pt BG}
                               {y' = transport ⟨BG⟩≡∥X∥ (pt BG)} {z' = ∣x∣'} {p = ⟨BG⟩≡∥X∥}
                               {q = refl} (transport-filler ⟨BG⟩≡∥X∥ (pt BG))
                               (uaβ ⟨BG⟩≃∥X∥ (pt BG)))
        ≡ compPathP'
            {p = ⟨BG⟩≡∥X∥}
            {q = refl}
            (congP (λ i → Bi≡tr∘Bi∘tr i) (transport-filler ⟨BG⟩≡∥X∥ (pt BG)))
            (congP (λ i → tr∘Bi∘tr≡Bi∘s i) (uaβ ⟨BG⟩≃∥X∥ (pt BG)))
    decompose₂ = congP-compPathP' {B = λ X → X} _ _ ⟨BG⟩≡∥X∥ _ _ (transport-filler ⟨BG⟩≡∥X∥ (pt BG)) _ refl _ (uaβ ⟨BG⟩≃∥X∥ (pt BG)) _ _ _ Bi≡tr∘Bi∘tr tr∘Bi∘tr≡Bi∘s
