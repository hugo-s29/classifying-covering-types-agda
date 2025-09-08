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
import SubgroupToCovering
import CoveringToSubgroup

module RightInv (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Path A (covering X∙ p p⋆ fib-set isCon)

  abstract
    path : PathP (λ i → p̃≡p i (x≡x̃ i) ≡ pt A) refl p⋆
    path = toPathP lem
      where

      lem : subst (λ x → x ≡ pt A) (λ i → p̃≡p i (x≡x̃ i)) refl ≡ p⋆
      lem =
          subst (λ x → x ≡ pt A) (λ i → p̃≡p i (x≡x̃ i)) refl
        ≡⟨ substInPathsR (λ i → p̃≡p i (x≡x̃ i)) refl ⟩
          congP (λ i → p̃≡p i) x≡x̃ ⁻¹ ∙ refl
        ≡⟨ rUnit _ ⁻¹ ⟩
          congP (λ i → p̃≡p i) x≡x̃ ⁻¹
        ≡⟨ cong sym p⋆-result ⟩
          p⋆ ∎

    lem-isCov : PathP (λ i → (a : ⟨ A ⟩) → isSet (fiber (p̃≡p i) a)) (SubgroupToCovering.coveringA A (CoveringToSubgroup.subgrp A (covering X∙ p p⋆ fib-set isCon)) .Covering.isCov) fib-set
    lem-isCov = isProp→PathP (λ _ → isPropΠ λ _ → isPropIsSet) _ _

    lem-isCon : PathP (λ i → isConnected' (X̃≡X i)) (SubgroupToCovering.coveringA A (CoveringToSubgroup.subgrp A (covering X∙ p p⋆ fib-set isCon)) .Covering.isCon) isCon
    lem-isCon = isProp→PathP (λ _ → isConnected'IsProp) _ _

    rightInv : SubgroupToCovering.coveringA A (CoveringToSubgroup.subgrp A (covering X∙ p p⋆ fib-set isCon)) ≡ covering X∙ p p⋆ fib-set isCon
    rightInv i .Covering.B .fst = X̃≡X i
    rightInv i .Covering.B .snd = x≡x̃ i
    rightInv i .Covering.f = p̃≡p i
    rightInv i .Covering.pt⋆ = path i
    rightInv i .Covering.isCov = lem-isCov i
    rightInv i .Covering.isCon = lem-isCon i
