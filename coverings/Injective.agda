open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-∥-rec ; map to ∥-∥-map ; elim to ∥-∥-elim)

-- Called "embedding" in the HoTT book
injective : {A B : Type} (f : A → B) → Type
injective {A} {B} f = {x y : A} →  isIso (cong {x = x} {y = y} f)

injective-fiber : {A B : Type} (f : A → B) → injective f → (b : B) → isProp (fiber f b)
injective-fiber {A} {B} f inj' b (x , p) (y , q) = ΣPathTransport→PathΣ _ _ (r , lemma r p q r-def) where

  inj : Iso (x ≡ y) (f x ≡ f y)
  inj = isIsoToIso inj'

  r : x ≡ y
  r = Iso.inv inj (p ∙ q ⁻¹)

  r-def : cong f r ≡ p ∙ q ⁻¹
  r-def = Iso.rightInv inj (p ∙ q ⁻¹)

  lemma : {a b : A} {y : B} (r : a ≡ b) (p : f a ≡ y) (q : f b ≡ y) → cong f r ≡ p ∙ q ⁻¹ → subst (λ x → f x ≡ y) r p ≡ q
  lemma {a} {b} {y} = J (λ b r → (p : f a ≡ y) (q : f b ≡ y) → cong f r ≡ p ∙ (q ⁻¹) → subst (λ x → f x ≡ y) r p ≡ q)
    (J (λ y p → (q : f a ≡ y) → cong f refl ≡ p ∙ (q ⁻¹) → subst (λ x → f x ≡ y) refl p ≡ q) (λ q h →
        subst (λ x₁ → f x₁ ≡ f a) refl refl
      ≡⟨ transportRefl refl ⟩
        refl
      ≡⟨ sym(lCancel q) ⟩
        q ⁻¹ ∙ q
      ≡⟨ lUnit (q ⁻¹ ∙ q) ⟩
        refl ∙ q ⁻¹ ∙ q
      ≡⟨ assoc _ _ _ ⟩
        (refl ∙ q ⁻¹) ∙ q
      ≡⟨ cong (_∙ q) (sym h) ⟩
        refl ∙ q
      ≡⟨ sym (lUnit q)⟩
        q ∎
    ))

im : {A B : Type} → (A → B) → Type
im {B = B} f = Σ B (λ b → ∥ fiber f b ∥₁)
