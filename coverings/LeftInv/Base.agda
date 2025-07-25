open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
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

module LeftInv.Base (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) (((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib) : SubGroupπ₁' A) where

  Bi∙ : BG B↪∙ (∥ A ∥∙ 3)
  Bi∙ = Bi , Bi-fib , Bi-⋆

  t : ⟨ BG ⟩ → ∥ pullbackΣ Bi ∣_∣ ∥ 3
  t g = ∥-∥ₕ-elim
    {B = λ a → Bi g ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
    (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3)
    (λ a r → ∣ g , a , r ∣)
    (Bi g)
    refl

  s : ∥ pullbackΣ Bi ∣_∣ ∥ 3 → ⟨ BG ⟩
  s = ∥-∥ₕ-elim
    {B = λ _ → ⟨ BG ⟩}
    (λ _ → grpBG)
    (λ (g , a , r) → g)

  t∘s : (x : ∥ pullbackΣ Bi ∣_∣ ∥ 3) → t (s x) ≡ x
  t∘s = ∥-∥ₕ-elim
    {B = λ x → t (s x) ≡ x}
    (λ x → isOfHLevelTruncPath {y = x})
    (λ (g , a , r) → cong₂ (∥-∥ₕ-elim {B = λ a → Bi g ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ g , a , r ∣)) r λ i j → r (i ∧ j))

  s∘t : (g : ⟨ BG ⟩) → s (t g) ≡ g
  s∘t g = ∥-∥ₕ-elim {B = λ a → (r : Bi g ≡ a) → s (∥-∥ₕ-elim {B = λ a → Bi g ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ g , a , r ∣) a r)  ≡ g}
    (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (grpBG _ _)) (λ _ _ → refl) (Bi g) refl

  ⟨BG⟩≅∥X∥ : ⟨ BG ⟩ ≅ (∥ pullbackΣ Bi ∣_∣ ∥ 3)
  ⟨BG⟩≅∥X∥ = iso t s t∘s s∘t

  ⟨BG⟩≃ᵇⁱ∥X∥ : BiInvEquiv ⟨ BG ⟩ (∥ pullbackΣ Bi ∣_∣ ∥ 3)
  ⟨BG⟩≃ᵇⁱ∥X∥ .BiInvEquiv.fun = t
  ⟨BG⟩≃ᵇⁱ∥X∥ .BiInvEquiv.invr = s
  ⟨BG⟩≃ᵇⁱ∥X∥ .BiInvEquiv.invr-rightInv = t∘s
  ⟨BG⟩≃ᵇⁱ∥X∥ .BiInvEquiv.invl = s
  ⟨BG⟩≃ᵇⁱ∥X∥ .BiInvEquiv.invl-leftInv = s∘t

  ⟨BG⟩≃∥X∥ : ⟨ BG ⟩ ≃ (∥ pullbackΣ Bi ∣_∣ ∥ 3)
  ⟨BG⟩≃∥X∥ = biInvEquiv→Equiv-left ⟨BG⟩≃ᵇⁱ∥X∥

  ⟨BG⟩≡∥X∥ : ⟨ BG ⟩ ≡ ∥ pullbackΣ Bi ∣_∣ ∥ 3
  ⟨BG⟩≡∥X∥ = ua ⟨BG⟩≃∥X∥

  ∥p∥ : ∥ pullbackΣ Bi ∣_∣ ∥ 3 → ∥ ⟨ A ⟩ ∥ 3
  ∥p∥ = ∥-∥ₕ-map (λ x → x .snd .fst)

  Bi∘s≡∥p∥ : Bi ∘ s ≡ ∥p∥
  Bi∘s≡∥p∥ = funExt (∥-∥ₕ-elim {B = λ x → Bi (s x) ≡ ∥p∥ x} (λ x → isOfHLevelTruncPath {y = ∥p∥ x}) (λ (_ , _ , q) → q))

  Bi≡tr∘Bi∘tr : PathP (λ i → ⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3) Bi (transport refl ∘ Bi ∘ transport⁻ ⟨BG⟩≡∥X∥)
  Bi≡tr∘Bi∘tr = funTypeTransp (λ X → X) (λ _ → ∥ ⟨ A ⟩ ∥ 3) ⟨BG⟩≡∥X∥ Bi

  tr∘Bi∘tr≡Bi∘s : transport refl ∘ Bi ∘ transport⁻ ⟨BG⟩≡∥X∥ ≡ Bi ∘ s
  tr∘Bi∘tr≡Bi∘s = funExt (λ x → transportRefl (Bi (transport⁻ ⟨BG⟩≡∥X∥ x)) ∙ cong Bi (~uaβ ⟨BG⟩≃∥X∥ x))

  Bi≡Bi∘s∙ : PathP (λ i → (⟨BG⟩≡∥X∥ ∙ refl) i → ∥ ⟨ A ⟩ ∥ 3) Bi (Bi ∘ s)
  Bi≡Bi∘s∙ = compPathP'
    {A = Type}
    {B = λ X → X → ∥ ⟨ A ⟩ ∥ 3}
    {x' = Bi}
    {y' = transport refl ∘ Bi ∘ (transport⁻ ⟨BG⟩≡∥X∥)}
    {z' = Bi ∘ s}
    {p = ⟨BG⟩≡∥X∥}
    {q = refl}
    Bi≡tr∘Bi∘tr
    tr∘Bi∘tr≡Bi∘s

  Bi≡Bi∘s : PathP (λ i → ⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3) Bi (Bi ∘ s)
  Bi≡Bi∘s = subst⁻ (λ x → PathP (λ i → x i → ∥ ⟨ A ⟩ ∥ 3) Bi (Bi ∘ s)) (rUnit ⟨BG⟩≡∥X∥) Bi≡Bi∘s∙

  Bi≡∥p∥∙ : PathP (λ i → (⟨BG⟩≡∥X∥ ∙ refl) i → ∥ ⟨ A ⟩ ∥ 3) Bi ∥p∥
  Bi≡∥p∥∙ = compPathP' {A = Type} {B = λ X → X → ∥ ⟨ A ⟩ ∥ 3}
    {x' = Bi}
    {y' = Bi ∘ s}
    {z' = ∥p∥}
    {p = ⟨BG⟩≡∥X∥}
    {q = refl}
    Bi≡Bi∘s
    Bi∘s≡∥p∥


  Bi≡∥p∥ : PathP (λ i → ⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3) Bi ∥p∥
  Bi≡∥p∥ = subst⁻ (λ r → PathP (λ i → r i → ∥ ⟨ A ⟩ ∥ 3) Bi ∥p∥) (rUnit ⟨BG⟩≡∥X∥) Bi≡∥p∥∙

  ∣x∣ : ∥ pullbackΣ Bi ∣_∣ ∥ 3
  ∣x∣ = ∣ pt BG , pt A , Bi-⋆ ∣

  ∣x∣' : ∥ pullbackΣ Bi ∣_∣ ∥ 3
  ∣x∣' = ∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) (Bi (pt BG)) refl

  ptBG≡∣x∣'∙ : PathP (λ i → (⟨BG⟩≡∥X∥ ∙ refl) i) (pt BG) ∣x∣'
  ptBG≡∣x∣'∙ =
    compPathP'
    {A = Type}
    {B = λ X → X}
    {x' = pt BG}
    {y' = transport ⟨BG⟩≡∥X∥ (pt BG)}
    {z' = ∣x∣'}
    {p = ⟨BG⟩≡∥X∥}
    {q = refl}
    (transport-filler ⟨BG⟩≡∥X∥ (pt BG))
    (uaβ ⟨BG⟩≃∥X∥ (pt BG))

  ptBG≡∣x∣' : PathP (λ i → ⟨BG⟩≡∥X∥ i) (pt BG) ∣x∣'
  ptBG≡∣x∣' = subst⁻ (λ u → PathP (λ i → u i) (pt BG) ∣x∣') (rUnit ⟨BG⟩≡∥X∥) ptBG≡∣x∣'∙


  ∣x∣'≡∣x∣ : ∣x∣' ≡ ∣x∣
  ∣x∣'≡∣x∣ = cong₂ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣)) Bi-⋆ (λ i j → Bi-⋆ (i ∧ j))

  ptBG≡∣x∣∙ : PathP (λ i → (⟨BG⟩≡∥X∥ ∙ refl) i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣
  ptBG≡∣x∣∙ = compPathP' {A = Type} {B = λ X → X}
    {x' = pt BG}
    {y' = ∣x∣'}
    {z' = ∣x∣}
    {p = ⟨BG⟩≡∥X∥} {q = refl}
    ptBG≡∣x∣'
    ∣x∣'≡∣x∣

  ptBG≡∣x∣ : PathP (λ i → ⟨BG⟩≡∥X∥ i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣
  ptBG≡∣x∣ = subst (λ r → PathP (λ i → r i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣) (rUnit ⟨BG⟩≡∥X∥ ⁻¹) ptBG≡∣x∣∙
