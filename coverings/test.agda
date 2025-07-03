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
open import Cubical.HITs.SetTruncation renaming (rec to ∥-∥₂-rec ; map to ∥-∥₂-map ; elim to ∥-∥₂-elim)
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-∥-rec ; map to ∥-∥-map ; map2 to ∥-∥-map2 ; elim to ∥-∥-elim ; elim2 to ∥-∥-elim2 ; elim3 to ∥-∥-elim3)
open import Cubical.Homotopy.Connected
open import Cubical.WildCat.Base

subst-snd : ∀ {ℓ} → {A : Type ℓ} (f : A → Type) (g : (x : A) → f x → Type) (x y : A) (p : x ≡ y) (u : Σ (f x) (g x)) →
  subst (λ x → Σ (f x) (g x)) p u ≡ ( subst f p (fst u) , transport (λ i → g (p i) (transport (λ j → f (p (i ∧ j))) (fst u))) (transport (cong (g x) (transportRefl (fst u) ⁻¹)) (snd u)) )
subst-snd f g x _ p u = J
  (λ y p → subst (λ x → Σ (f x) (g x)) p u ≡ ( subst f p (fst u) , transport (λ i → g (p i) (transport (λ j → f (p (i ∧ j))) (fst u))) (transport (cong (g x) (transportRefl (fst u) ⁻¹)) (snd u)) ))
  (
    ΣPathTransport→PathΣ _ _ ((
        fst (subst (λ x₁ → Σ (f x₁) (g x₁)) refl u)
      ≡⟨ cong fst (transportRefl u) ⟩
        fst u
      ≡⟨ transportRefl (fst u) ⁻¹ ⟩
        subst f refl (fst u) ∎
    ) , (
        transport (λ i → g x (step-≡ (fst (subst (λ x₁ → Σ (f x₁) (g x₁)) (λ _ → x) u)) (step-≡ (fst u) (subst f (λ _ → x) (fst u) ∎) (transportRefl (fst u) ⁻¹)) (λ i₁ → fst (transportRefl u i₁)) i)) (transp (λ i → Σ (f (refl i)) (g (refl i))) i0 u .snd)
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ {!!} ⟩
        transport refl (transport (λ i → g x ((transportRefl (fst u) ⁻¹) i)) (snd u)) ∎
    )
  ))
  p
