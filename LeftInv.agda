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
open import Paths
import SubgroupToCovering
import CoveringToSubgroup

module LeftInv (A : Pointed ℓ-zero) ((subgroup BG Bi Bi-⋆ isBi isCon grpBG) : SubGroupπ₁ A) where
  open import LeftInv.Base A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)
  open import LeftInv.Path A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)

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

    lem-isBi : PathP (λ i → (a : ∥ ⟨ A ⟩ ∥ 3) → isSet (fiber (Bi≡∥p∥ i) a)) isBi (CoveringToSubgroup.subgrp A (SubgroupToCovering.coveringA A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)) .SubGroupπ₁.isBi)
    lem-isBi = isProp→PathP (λ _ → isPropΠ (λ _ → isPropIsSet)) _ _

    lem-isCon : PathP (λ i → isConnected' (⟨BG⟩≡∥X∥ i)) isCon (CoveringToSubgroup.subgrp A (SubgroupToCovering.coveringA A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)) .SubGroupπ₁.isCon)
    lem-isCon = isProp→PathP (λ _ → isConnected'IsProp) _ _

    lem-isGrp : PathP (λ i → isGroupoid (⟨BG⟩≡∥X∥ i)) grpBG (CoveringToSubgroup.subgrp A (SubgroupToCovering.coveringA A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)) .SubGroupπ₁.isGrp)
    lem-isGrp = isProp→PathP (λ _ → isPropIsGroupoid) _ _
   
    leftInv : CoveringToSubgroup.subgrp A (SubgroupToCovering.coveringA A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)) ≡ subgroup BG Bi Bi-⋆ isBi isCon grpBG
    leftInv i .SubGroupπ₁.BG .fst = ⟨BG⟩≡∥X∥ (~ i)
    leftInv i .SubGroupπ₁.BG .snd = ptBG≡∣x∣ (~ i)
    leftInv i .SubGroupπ₁.Bi = Bi≡∥p∥ (~ i)
    leftInv i .SubGroupπ₁.Bi⋆ = path (~ i)
    leftInv i .SubGroupπ₁.isBi = lem-isBi (~ i)
    leftInv i .SubGroupπ₁.isCon = lem-isCon (~ i)
    leftInv i .SubGroupπ₁.isGrp = lem-isGrp (~ i)
