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

module LeftInv.Path (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) (((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib) : SubGroupπ₁' A) where
  open import LeftInv.Base A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)
  open import LeftInv.Part1 A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)
  open import LeftInv.Part2 A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)
  open import LeftInv.Part3 A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)
  open import LeftInv.Decompose1 A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)
  open import LeftInv.Decompose2 A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)

  abstract
    part1 : congP (λ i → Bi≡tr∘Bi∘tr i) (transport-filler ⟨BG⟩≡∥X∥ (pt BG)) ≡
      cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹
      ∙ transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ (transport ⟨BG⟩≡∥X∥ (pt BG)))) ⁻¹
    part1 = congP1

    {-# NOINLINE part1 #-}

    part2 : congP (λ i → tr∘Bi∘tr≡Bi∘s i) (uaβ ⟨BG⟩≃∥X∥ (pt BG)) ≡
      transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
      ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
      ∙ cong Bi (s∘t (pt BG)) ⁻¹
    part2 = congP2

    {-# NOINLINE part2 #-}

    part3 : congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣ ≡ cong Bi (s∘t (pt BG) ) ∙ Bi-⋆
    part3 = congP3

    {-# NOINLINE part3 #-}

  Bi⋆-result' : congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣' ≡ cong Bi (s∘t (pt BG)) ⁻¹
  Bi⋆-result' =
        congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣'
    ≡⟨ congP-subst-rUnit ⟨BG⟩≡∥X∥ Bi≡Bi∘s∙ ptBG≡∣x∣'∙ ⟩
        congP (λ i → Bi≡Bi∘s∙ i) ptBG≡∣x∣'∙
    ≡⟨ decompose₂ ⟩
        compPathP'
        {p = ⟨BG⟩≡∥X∥}
        {q = refl}
        (congP (λ i → Bi≡tr∘Bi∘tr i) (transport-filler ⟨BG⟩≡∥X∥ (pt BG)))
        (congP (λ i → tr∘Bi∘tr≡Bi∘s i) (uaβ ⟨BG⟩≃∥X∥ (pt BG)))
    ≡⟨ compPathP'-nondep {r = ⟨BG⟩≡∥X∥} {s = refl} (congP (λ i → Bi≡tr∘Bi∘tr i) (transport-filler ⟨BG⟩≡∥X∥ (pt BG))) (congP (λ i → tr∘Bi∘tr≡Bi∘s i) (uaβ ⟨BG⟩≃∥X∥ (pt BG))) ⟩
        congP (λ i → Bi≡tr∘Bi∘tr i) (transport-filler ⟨BG⟩≡∥X∥ (pt BG))
        ∙ congP (λ i → tr∘Bi∘tr≡Bi∘s i) (uaβ ⟨BG⟩≃∥X∥ (pt BG))
    ≡⟨ cong₂ _∙_ part1 part2 ⟩
        (cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹
        ∙ transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ (transport ⟨BG⟩≡∥X∥ (pt BG)))) ⁻¹)
        ∙ transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
        ∙ cong Bi (s∘t (pt BG)) ⁻¹
    ≡⟨ assoc _ _ _ ⁻¹ ⟩
        cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹
        ∙ transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ (transport ⟨BG⟩≡∥X∥ (pt BG)))) ⁻¹
        ∙ transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG))))
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
        ∙ cong Bi (s∘t (pt BG)) ⁻¹
    ≡⟨ cong (cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹ ∙_) (assoc _ _ _) ⟩
        cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹
        ∙ (transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ (transport ⟨BG⟩≡∥X∥ (pt BG)))) ⁻¹
        ∙ transportRefl (Bi (transport⁻ (ua ⟨BG⟩≃∥X∥) (transport (ua ⟨BG⟩≃∥X∥) (pt BG)))))
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
        ∙ cong Bi (s∘t (pt BG)) ⁻¹
    ≡⟨ cong (λ u → cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹ ∙ u ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG)) ∙ cong Bi (s∘t (pt BG)) ⁻¹) (lCancel _) ⟩
        cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹
        ∙ refl
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
        ∙ cong Bi (s∘t (pt BG)) ⁻¹
    ≡⟨ cong (cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹ ∙_) (lUnit _) ⁻¹ ⟩
        cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹
        ∙ cong Bi (transport⁻Transport (ua ⟨BG⟩≃∥X∥) (pt BG))
        ∙ cong Bi (s∘t (pt BG)) ⁻¹
    ≡⟨ assoc _ _ _ ⟩
        (cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)) ⁻¹
        ∙ cong Bi (transport⁻Transport ⟨BG⟩≡∥X∥ (pt BG)))
        ∙ cong Bi (s∘t (pt BG)) ⁻¹
    ≡⟨ cong (_∙ cong Bi (s∘t (pt BG)) ⁻¹) (lCancel _) ⟩
        refl ∙ cong Bi (s∘t (pt BG)) ⁻¹
    ≡⟨ lUnit _ ⁻¹ ⟩
        cong Bi (s∘t (pt BG)) ⁻¹ ∎

  Bi⋆-result : congP (λ i → Bi≡∥p∥ i) ptBG≡∣x∣ ≡ Bi-⋆
  Bi⋆-result =
        congP (λ i → Bi≡∥p∥ i) ptBG≡∣x∣
    ≡⟨ congP-subst-rUnit ⟨BG⟩≡∥X∥ Bi≡∥p∥∙ ptBG≡∣x∣∙ ⟩
        congP (λ i → Bi≡∥p∥∙ i) ptBG≡∣x∣∙
    ≡⟨ decompose₁ ⟩
        compPathP'
        {p = ⟨BG⟩≡∥X∥}
        {q = refl}
        (congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣')
        (congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣)
    ≡⟨ compPathP'-nondep {r = ⟨BG⟩≡∥X∥} {s = refl} (congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣') (congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣) ⟩
        congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣'
        ∙ congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣
    ≡⟨ cong₂ _∙_ Bi⋆-result' part3 ⟩
      cong Bi (s∘t (pt BG)) ⁻¹ ∙ cong Bi (s∘t (pt BG) ) ∙ Bi-⋆
    ≡⟨ assoc _ _ _ ⟩
      (cong Bi (s∘t (pt BG)) ⁻¹ ∙ cong Bi (s∘t (pt BG))) ∙ Bi-⋆
    ≡⟨ cong (_∙ Bi-⋆) (lCancel _) ⟩
      refl ∙ Bi-⋆
    ≡⟨ lUnit _ ⁻¹ ⟩
      Bi-⋆ ∎
