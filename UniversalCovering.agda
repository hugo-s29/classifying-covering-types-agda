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

module UniversalCovering (A∙ : Pointed ℓ-zero) (_ : isConnected' ⟨ A∙ ⟩) where
  A = ⟨ A∙ ⟩
  ⋆A = pt A∙

  Ã = Σ A (λ a → ∥ ⋆A ≡ a ∥ 2)

  1-connected : isConnected 3 Ã
  1-connected = ∣ ⋆A , ∣ refl ∣ ∣ , ∥-∥ₕ-elim {B = λ y → ∣ ⋆A , ∣ refl ∣ ∣ ≡ y} (λ y → isOfHLevelTruncPath {y = y})
    (λ (a , p) → transport⁻ (PathIdTrunc 2) (∥-∥ₕ-elim {B = λ p → ∥ (⋆A , ∣ refl ∣) ≡ (a , p) ∥ 2} (λ _ → isOfHLevelTrunc 2)
      (J (λ a p → ∥ (⋆A , ∣ refl ∣) ≡ (a , ∣ p ∣) ∥ 2) ∣ refl ∣) p))

  connected : isConnected' Ã
  connected = ∣ (⋆A , ∣ refl ∣) ∣₁ , lemma₂ where

    lemma₀ : (a b : A) (p : ⋆A ≡ a) (q : ⋆A ≡ b) → (a , ∣ p ∣) ≡ (b , ∣ q ∣)
    lemma₀ a b = J (λ a p → (q : ⋆A ≡ b) → (a , ∣ p ∣) ≡ (b , ∣ q ∣)) (J (λ b q → (⋆A , ∣ refl ∣) ≡ (b , ∣ q ∣)) refl)

    lemma₁ : (a : A) (p : ⋆A ≡ a) (y : Ã) → ∥ (a , ∣ p ∣) ≡ y ∥₁
    lemma₁ a p (b , q) = ∥-∥ₕ-elim {B = λ q → ∥ (a , ∣ p ∣) ≡ (b , q) ∥₁} (λ _ → isProp→isSet isPropPropTrunc) (λ q → ∣ lemma₀ a b p q ∣₁) q

    lemma₂ : (x y : Ã) → ∥ x ≡ y ∥₁
    lemma₂ (a , p) = ∥-∥ₕ-elim {B = λ p → (y : Ã) → ∥ (a , p) ≡ y ∥₁} (λ _ → isProp→isSet (isPropΠ (λ _ → isPropPropTrunc))) (lemma₁ a) p
