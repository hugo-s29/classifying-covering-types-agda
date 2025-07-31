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

module RightInv (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where
  open import RightInv.Base A conA (((X , x) , p) , p⋆ , hypCon , fib-set)

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
        ≡⟨ {!!} ⟩
          p⋆ ∎



  rightInv :
    let ((BG , Bi), Bi-⋆ , conBG , grpBG , fib-set') = CoveringToSubgroup.subgroup A (((X , x) , p) , p⋆ , hypCon , fib-set) in
    SubgroupToCovering.connectedCovering₀ A BG conA conBG (Bi , fib-set' , Bi-⋆) ≡ (((X , x), p), p⋆ , hypCon , fib-set)
  rightInv = ΣPathP ((ΣPathP ((ΣPathP (X̃≡X , x≡x̃)) , p̃≡p)) , ΣPathP ({!!} , toPathP (isProp× isConnected'IsProp (isPropΠ (λ _ → isPropIsSet)) _ _)))
