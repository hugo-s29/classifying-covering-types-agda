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
open import Base
open import Pullback
open import Paths
open import UniversalCovering
import SubgroupToCovering
import CoveringToSubgroup

module RightInv.Base (A : Pointed ℓ-zero) ((covering X∙ p p⋆ fib-set isCon) : Covering A) where
  X = ⟨ X∙ ⟩

  ∥p∥ : ∥ X ∥ 3 → ∥ ⟨ A ⟩ ∥ 3
  ∥p∥ = ∥-∥ₕ-map p

  X̃ = pullbackΣ {B = ⟨ A ⟩} ∥p∥ ∣_∣

  p̃ : X̃ → ⟨ A ⟩
  p̃ (_ , a , _) = a

  e : X → X̃
  e x = ∣ x ∣ , p x , refl

  e'-fib : (a : ⟨ A ⟩) → fiber p̃ a → fiber p a
  e'-fib a₀ ((x , a , q) , r) =
    ∥-∥ₕ-elim
      {B = λ x → (q : ∥p∥ x ≡ ∣ a ∣) → fiber p a₀}
      (λ _ → isGroupoidΠ (λ _ → isSet→isGroupoid (fib-set a₀)))
      (λ x q →
        ∥-∥ₕ-elim
        {B = λ _ → fiber p a₀}
        (λ _ → fib-set a₀)
        (λ q → x , q ∙ r)
        (transport (PathIdTrunc 2) q)
      )
      x q

  e' : X̃ → X
  e' x̃ = e'-fib (p̃ x̃) (x̃ , refl) .fst

  e'∘e : (x : X) → e' (e x) ≡ x
  e'∘e x = refl

  fibp̃-isSet : (a : ⟨ A ⟩) → isSet (fiber p̃ a)
  fibp̃-isSet = SubgroupToCovering.p-isCov A (CoveringToSubgroup.subgrp A (covering X∙ p p⋆ fib-set isCon))

  e∘e'-mini-lemma : (x : X) (a : ⟨ A ⟩) (q : ∣ p x ∣ ≡ ∣ a ∣) →
    (e (e' (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) (transport (PathIdTrunc 2) q))) , e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) (transport (PathIdTrunc 2) q)) , refl) .snd)
    ≡ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) (transport (PathIdTrunc 2) q)) , (λ _ → p̃ (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) (transport (PathIdTrunc 2) q))))
  e∘e'-mini-lemma x a q =
      ∥-∥ₕ-elim
      {B = λ q → (e (e' (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q)) , (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q) , refl)) .snd) ≡ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q), refl)}
      (λ _ → isProp→isSet (fibp̃-isSet a _ _))
      (λ q →
            e (e' (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣)) , e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd
          ≡⟨ cong {B = λ _ → fiber p̃ a}
          (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                  (λ q → x , q ∙ refl) u .fst) ,
                      ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                      (λ q → x , q ∙ refl) u .snd) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
          ⟩
              e x , q ∙ refl
          ≡⟨ cong {B = λ _ → fiber p̃ a} ( e x ,_ ) (rUnit q) ⁻¹ ⟩
              e x , q
          ≡⟨ cong₃ {A = ⟨ A ⟩} {B = λ a → ∥p∥ ∣ x ∣ ≡ ∣ a ∣} {C = λ a' _ → a' ≡ a} {D = λ _ _ _ → fiber p̃ a}
              (λ u v w → (∣ x ∣ , u , v) , w) q (λ i j → ∣ q (i ∧ j) ∣) (λ i j → q (i ∨ j))
          ⟩
              (∣ x ∣ , a , cong ∣_∣ q) , refl
          ≡⟨ cong {A = ∣ p x ∣ ≡ ∣ a ∣} {B = λ _ → fiber p̃ a }
              (λ u → (∣ x ∣ , a , u) , refl) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹
          ⟩
            (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl ∎
      ) (transport (PathIdTrunc 2) q)

  e∘e'-lemma : (x̃ : X̃) → (e (e' x̃) , e'-fib (p̃ x̃) (x̃ , refl) .snd) ≡ (x̃  , refl)
  e∘e'-lemma (∣x∣ , a , q) =
        ∥-∥ₕ-elim {B = λ ∣x∣ → (q : ∥p∥ ∣x∣ ≡ ∣ a ∣) → (e (e' (∣x∣ , a , q)) , e'-fib a ((∣x∣ , a , q) , refl) .snd) ≡ ((∣x∣ , a , q) , refl)}
            (λ ∣x∣ → isOfHLevelΠ 3 λ q → isSet→isGroupoid (isProp→isSet (fibp̃-isSet (p̃ (∣x∣ , a , q)) _ _)))
            (λ x q →
              subst (λ q → (e (e' (∣ x ∣ₕ , a , q)) , e'-fib a ((∣ x ∣ₕ , a , q) , refl) .snd) ≡ ((∣ x ∣ₕ , a , q) , refl)  )
              (transport⁻Transport (PathIdTrunc 2) q)
              (e∘e'-mini-lemma x a q)
            ) ∣x∣ q

  e∘e' : (x̃ : X̃) → e (e' x̃) ≡ x̃
  e∘e' x̃ = cong fst (e∘e'-lemma x̃)

  X̃≃ᵇⁱX : BiInvEquiv X̃ X
  X̃≃ᵇⁱX .BiInvEquiv.fun = e'
  X̃≃ᵇⁱX .BiInvEquiv.invr = e
  X̃≃ᵇⁱX .BiInvEquiv.invr-rightInv = e'∘e
  X̃≃ᵇⁱX .BiInvEquiv.invl = e
  X̃≃ᵇⁱX .BiInvEquiv.invl-leftInv = e∘e'

  X̃≃X : X̃ ≃ X
  X̃≃X = biInvEquiv→Equiv-left X̃≃ᵇⁱX

  X̃≡X : X̃ ≡ X
  X̃≡X = ua X̃≃X

  x̃ : X̃
  x̃ = ∣ pt X∙ ∣ , pt A , cong ∣_∣ p⋆

  x̃≡tr-x̃ : PathP (λ i → X̃≡X i) x̃ (transport X̃≡X x̃)
  x̃≡tr-x̃ = transport-filler X̃≡X x̃

  tr-x̃≡e'x̃ : transport X̃≡X x̃ ≡ e' x̃
  tr-x̃≡e'x̃ = uaβ X̃≃X x̃

  e'x̃≡x : e' x̃ ≡ pt X∙
  e'x̃≡x = refl

  x≡x̃∙ : PathP (λ i → (X̃≡X ∙ refl) i) x̃ (pt X∙)
  x≡x̃∙ = compPathP'
    {A = Type}
    {B = λ x → x}
    {x' = x̃}
    {y' = transport X̃≡X x̃}
    {z' = pt X∙}
    {p = X̃≡X}
    {q = refl}
    x̃≡tr-x̃
    tr-x̃≡e'x̃

  x≡x̃ : PathP (λ i → X̃≡X i) x̃ (pt X∙)
  x≡x̃ = subst⁻ (λ u → PathP (λ i → u i) x̃ (pt X∙)) (rUnit X̃≡X) x≡x̃∙

  p̃≡tr∘p̃∘tr : PathP (λ i → X̃≡X i → ⟨ A ⟩) p̃ (transport refl ∘ p̃ ∘ transport⁻ X̃≡X)
  p̃≡tr∘p̃∘tr = funTypeTransp (λ X → X) (λ _ → ⟨ A ⟩) X̃≡X p̃

  tr∘p̃∘tr≡p̃∘e : transport refl ∘ p̃ ∘ transport⁻ X̃≡X ≡ p̃ ∘ e
  tr∘p̃∘tr≡p̃∘e = funExt (λ x → transportRefl (p̃ (transport⁻ X̃≡X x)) ∙ cong p̃ (~uaβ X̃≃X x))

  p̃∘e≡p : p̃ ∘ e ≡ p
  p̃∘e≡p = refl

  p̃≡p∙ : PathP (λ i → (X̃≡X ∙ refl) i → ⟨ A ⟩) p̃ p
  p̃≡p∙ =
    compPathP'
    {A = Type}
    {B = λ x → x → ⟨ A ⟩}
    {x' = p̃}
    {y' = transport refl ∘ p̃ ∘ transport⁻ X̃≡X}
    {z' = p}
    {p = X̃≡X}
    {q = refl}
    p̃≡tr∘p̃∘tr
    tr∘p̃∘tr≡p̃∘e

  p̃≡p : PathP (λ i → X̃≡X i → ⟨ A ⟩) p̃ p
  p̃≡p = subst⁻ (λ u → PathP (λ i → u i → ⟨ A ⟩) p̃ p) (rUnit X̃≡X) p̃≡p∙

  postulate
    tr∘tr∘tr-refl : {A : Type} (x : A) → cong (transport refl) (transport⁻Transport refl x) ≡ transportTransport⁻ refl (transport refl x)
    {-
    Proving that is giving a path from
    λ i → transport refl (transportRefl (transportRefl x i) i)
    to
    λ i → transportRefl (transportRefl (transport refl x) i) i
    which seems easy enough (and yet, I tried and can't do it).
    This is true in classical HoTT because
    transport refl x = x
    transport⁻Transport refl u = refl {x = u}
    transportTransport⁻ refl u = refl {x = u}
    because it's defined by path induction.
    So, this result, it's just:
        cong id refl ≡ refl {x = x}
    which is given by refl.

    I'm admitting it, but if a Cubical proof exists, then I'll gladly add it here.
    -}

  abstract
    tr∘tr∘tr :
        {A B C : Type}
        (p : A ≡ B)
        (f : B → C)
        (x : A)
        → cong (f ∘ transport p) (transport⁻Transport p x) ≡ cong f (transportTransport⁻ p (transport p x))
    tr∘tr∘tr {A = A} {C = C} = J (λ B p →
        (f : B → C) (x : A) → cong (f ∘ transport p) (transport⁻Transport p x) ≡ cong f (transportTransport⁻ p (transport p x))
        ) λ f → cong (cong f) ∘ tr∘tr∘tr-refl
