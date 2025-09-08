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

module LeftInv.Part2 (A : Pointed ℓ-zero) ((subgroup BG Bi Bi-⋆ isBi isCon grpBG) : SubGroupπ₁ A) where
  open import LeftInv.Base A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)

  abstract
    lemma : (x : ∥ pullbackΣ Bi ∣_∣ ∥ 3) → cong s (t∘s x) ≡ s∘t (s x)
    lemma = ∥-∥ₕ-elim
      {B = λ x → cong s (t∘s x) ≡ s∘t (s x)}
      (λ x → isSet→isGroupoid (isProp→isSet (grpBG _ _ _ _)))
      λ (g , a , r) → lem g a r
      where

      minipart1 : (g : ⟨ BG ⟩) (a : ⟨ A ⟩) (r : Bi g ≡ ∣ a ∣) → PathP (λ i → s (t∘s ∣ g , a , r ∣ i) ≡ g) (cong s (t∘s ∣ g , a , r ∣)) refl
      minipart1 g a r i j = s (t∘s ∣ g , a , r ∣ (i ∨ j))

      minipart2 : (g : ⟨ BG ⟩) (a : ⟨ A ⟩) (r : Bi g ≡ ∣ a ∣) → PathP (λ i → s ((t∘s ∣ g , a , r ∣ ⁻¹) i) ≡ g) refl (s∘t g)
      minipart2 g a r = symP (
          cong₂ (∥-∥ₕ-elim {B = λ a → (r : Bi g ≡ a) → s (∥-∥ₕ-elim {B = λ a → Bi g ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
          (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ g , a , r ∣) a r)  ≡ g}
          (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (grpBG _ _)) λ _ _ → refl)
          r
          λ i j → r (i ∧ j)
        )

      lem∙ : (g : ⟨ BG ⟩) (a : ⟨ A ⟩) (r : Bi g ≡ ∣ a ∣) → PathP (λ i → s ((t∘s ∣ g , a , r ∣ ∙ t∘s ∣ g , a , r ∣ ⁻¹) i) ≡ g) (cong s (t∘s ∣ g , a , r ∣)) (s∘t g)
      lem∙ g a r = compPathP'
        {A = ∥ pullbackΣ Bi ∣_∣ ∥ 3}
        {B = λ u → s u ≡ g }
        {x' = cong s (t∘s ∣ g , a , r ∣)}
        {y' = refl}
        {z' = s∘t g}
        {p = t∘s ∣ g , a , r ∣}
        {q = t∘s ∣ g , a , r ∣ ⁻¹}
        (minipart1 g a r)
        (minipart2 g a r)

      lem : (g : ⟨ BG ⟩) (a : ⟨ A ⟩) (r : Bi g ≡ ∣ a ∣) → cong s (t∘s ∣ g , a , r ∣) ≡ s∘t g
      lem g a r = subst (λ u → PathP (λ i → s (u i) ≡ g) (cong s (t∘s ∣ g , a , r ∣)) (s∘t g)) (rCancel (t∘s ∣ g , a , r ∣)) (lem∙ g a r)

    retEq≡s∘t : (g : ⟨ BG ⟩) → retEq ⟨BG⟩≃∥X∥ g ≡ s∘t g
    retEq≡s∘t g = retEq≡linv t s t∘s s∘t lemma g

    congP2 : congP (λ i → tr∘Bi∘tr≡Bi∘s i) (uaβ ⟨BG⟩≃∥X∥ (pt BG)) ≡
      transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
      ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
      ∙ cong Bi (s∘t (pt BG)) ⁻¹
    congP2 =
        congP (λ i → tr∘Bi∘tr≡Bi∘s i) (uaβ ⟨BG⟩≃∥X∥ (pt BG))
      ≡⟨ cong (congP (λ i → tr∘Bi∘tr≡Bi∘s i)) (lUnit (uaβ ⟨BG⟩≃∥X∥ (pt BG))) ⟩
        congP (λ i x → (transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ x)) ∙ cong Bi (~uaβ ⟨BG⟩≃∥X∥ x)) i) (refl ∙ uaβ ⟨BG⟩≃∥X∥ (pt BG))
      ≡⟨ congP∙ (λ i x → transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ x)) i) (λ i x → cong Bi (~uaβ ⟨BG⟩≃∥X∥ x) i) refl (uaβ ⟨BG⟩≃∥X∥ (pt BG)) ⟩
        congP (λ i x → transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ x)) i) (refl {x = transport (ua ⟨BG⟩≃∥X∥) (pt BG)})
        ∙ congP (λ i x → cong Bi (~uaβ ⟨BG⟩≃∥X∥ x) i) (uaβ ⟨BG⟩≃∥X∥ (pt BG))
      ≡⟨⟩
        transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
        ∙ cong Bi (congP (λ i x → ~uaβ ⟨BG⟩≃∥X∥ x i) (uaβ ⟨BG⟩≃∥X∥ (pt BG)))
      ≡⟨ cong (λ u → transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ (transport (ua ⟨BG⟩≃∥X∥) (pt BG)))) ∙ cong Bi u) (ua-tr⁻Tr ⟨BG⟩≃∥X∥ (pt BG)) ⟩
        transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG) ∙ retEq ⟨BG⟩≃∥X∥ (pt BG) ⁻¹)
      ≡⟨ cong (λ u → transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG)))) ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG) ∙ u ⁻¹)) (retEq≡s∘t (pt BG)) ⟩
        transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG) ∙ s∘t (pt BG) ⁻¹)
      ≡⟨ cong (transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG)))) ∙_) (cong∙ Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG)) (s∘t (pt BG) ⁻¹)) ⟩
        transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
        ∙ cong Bi (s∘t (pt BG)) ⁻¹ ∎
