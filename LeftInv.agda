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
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim ; map2 to ∥-∥ₕ-map2 ; elim2 to ∥-∥ₕ-elim2)
open import Base
import SubgroupToCovering
import CoveringToSubgroup

module LeftInv (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) (((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib) : SubGroupπ₁' A) where
  open import LeftInv.Base A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)
  open import LeftInv.Path A conA ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)

  abstract
    path : PathP (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i) ≡ ∣ pt A ∣) Bi-⋆ refl
    path = toPathP lem
        where

        lem : transport (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i) ≡ ∣ pt A ∣) Bi-⋆ ≡ refl
        lem =
                subst (λ x → x ≡ ∣ pt A ∣) (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) Bi-⋆
            ≡⟨ substInPathsR (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) Bi-⋆ ⟩
                congP (λ i → Bi≡∥p∥ i) ptBG≡∣x∣ ⁻¹ ∙ Bi-⋆
            ≡⟨ cong (λ u → u ⁻¹ ∙ Bi-⋆) Bi⋆-result ⟩
                Bi-⋆ ⁻¹ ∙ Bi-⋆
            ≡⟨ lCancel _ ⟩
                refl ∎

    leftInv : CoveringToSubgroup.subgroup A (SubgroupToCovering.connectedCovering₀ A BG conA conBG (Bi , Bi-fib , Bi-⋆))
        ≡ ((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib)
    leftInv = ΣPathP ((ΣPathP ((ΣPathP (⟨BG⟩≡∥X∥ , ptBG≡∣x∣)) , Bi≡∥p∥)) , ΣPathP (path , toPathP (isProp× isConnected'IsProp (isProp× isPropIsGroupoid (isPropΠ (λ _ → isPropIsSet))) _ _))) ⁻¹
