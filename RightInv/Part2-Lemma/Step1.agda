open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim ; map2 to ∥-∥ₕ-map2 ; elim2 to ∥-∥ₕ-elim2)
open import Base

module RightInv.Part2-Lemma.Step1 (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) (x : ⟨ X∙ ⟩) where
  open import RightInv.Base A (covering X∙ p p⋆ fib-set isCon)
  open import RightInv.Part2-Lemma.Base A (covering X∙ p p⋆ fib-set isCon) x

  abstract
    cong-fst-subst :
        {A C : Type}
        {B : A → Type}
        {f g : C → Σ A B}
        {c c' : C}
        (q : f c ≡ g c)
        (p : c ≡ c')
        →
        cong fst (subst (λ x → f x ≡ g x) p q) ≡ subst (λ x → f x .fst ≡ g x .fst) p (cong fst q)
    cong-fst-subst {f = f} {g = g} q = J (λ c' p → cong fst (subst (λ x → f x ≡ g x) p q) ≡ subst (λ x → f x .fst ≡ g x .fst) p (cong fst q)) (
        cong fst (transport refl q)
        ≡⟨ cong (cong fst) (transportRefl q) ⟩
        cong fst q
        ≡⟨ transportRefl (cong fst q) ⁻¹ ⟩
        transport refl (cong fst q) ∎
        )

    step₁ : cong fst (subst (λ q → Path (fiber p̃ a) (e (e' (∣ x ∣ , a , q)) , e'-fib a ((∣ x ∣ , a , q) , refl {x = p x}) .snd) ((∣ x ∣ₕ , a , q) , refl))
        (transport⁻Transport (PathIdTrunc 2) refl) (e∘e'-mini-lemma x a refl))
        ≡ subst (λ q → e (e' (∣ x ∣ , a , q)) ≡ (∣ x ∣ , a , q) ) (transport⁻Transport (PathIdTrunc 2) refl) (cong fst (e∘e'-mini-lemma x a refl))
    step₁ = cong-fst-subst {f = λ q → (e (e' (∣ x ∣ , a , q)) , e'-fib a ((∣ x ∣ , a , q) , refl {x = p x}) .snd)} {g = λ q → (∣ x ∣ , a , q), refl} (e∘e'-mini-lemma x a refl) (transport⁻Transport (PathIdTrunc {a = a} 2) refl)
