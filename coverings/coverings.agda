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

module RightInv (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where

  ∥p∥ : ∥ X ∥ 3 → ∥ ⟨ A ⟩ ∥ 3
  ∥p∥ = ∥-∥ₕ-map p

  X̃ = pullbackΣ {B = ⟨ A ⟩} ∥p∥ ∣_∣

  p̃ : X̃ → ⟨ A ⟩
  p̃ (_ , a , _) = a

  e : X → X̃
  e x = ∣ x ∣ , p x , refl

  e-fib : (a : ⟨ A ⟩) → fiber p a → fiber p̃ a
  e-fib _ (x , q) = (∣ x ∣ , p x , refl) , q

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

  e'∘e : (a : ⟨ A ⟩) (x : X) (q : p x ≡ a) → e'-fib a (e-fib a (x , q)) ≡ (x , q)
  e'∘e a x q =
      ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ r → x , r ∙ q) (transport (PathIdTrunc 2) refl)
    ≡⟨ cong (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ r → x , r ∙ q)) (transportIsoToPath (PathIdTruncIso 2) refl ∙ transportRefl ∣ refl ∣) ⟩
      x , refl ∙ q
    ≡⟨ cong (λ q → x , q) (lUnit q ⁻¹) ⟩
      x , q ∎

  fibp̃-isSet : (a : ⟨ A ⟩) → isSet (fiber p̃ a)
  fibp̃-isSet a = Subgroup→PCCovering₀.p-isCov₀ A (∥ X , x ∥∙ 3) conA (PCCovering₀→Subgroup.connected A (((X , x) , p) , p⋆ , hypCon , fib-set)) (PCCovering₀→Subgroup.Bi∙ A (((X , x) , p) , (p⋆ , hypCon , fib-set))) a

  e∘e' : (a₀ : ⟨ A ⟩) (a : ⟨ A ⟩) (x : ∥ X ∥ 3) (q : ∥p∥ x ≡ ∣ a ∣) (r : a ≡ a₀) → e-fib a₀ (e'-fib a₀ ((x , a , q) , r)) ≡ ((x , a , q) , r)
  e∘e' a₀ a x q r =
    ∥-∥ₕ-elim
    {B = λ x → (q : ∥p∥ x ≡ ∣ a ∣) → e-fib a₀ (e'-fib a₀ ((x , a , q) , r)) ≡ ((x , a , q) , r)}
    (λ x → isGroupoidΠ (λ q → isSet→isGroupoid (isProp→isSet (fibp̃-isSet a₀ _ _))))
    (λ x q →
      subst (λ q → e-fib a₀ (e'-fib a₀ ((∣ x ∣ , a , q) , r)) ≡ ((∣ x ∣ , a , q) , r)) (transport⁻Transport (PathIdTrunc 2) q)
      (∥-∥ₕ-elim
        {B = λ q → e-fib a₀ (e'-fib a₀ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q) , r)) ≡ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q), r)}
        (λ _ → isProp→isSet (fibp̃-isSet a₀ _ _))
        (λ q →
          J (λ a q → (r : a ≡ a₀) → e-fib a₀ (e'-fib a₀ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , r)) ≡ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , r))
          (λ r →
            e-fib a₀ (e'-fib a₀ ((∣ x ∣ , p x , transport⁻ (PathIdTrunc 2) ∣ refl ∣) , r))
          ≡⟨⟩
            e-fib a₀ (∥-∥ₕ-elim {B = λ _ → fiber p a₀} (λ _ → fib-set a₀) (λ q → x , q ∙ r) (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ refl ∣)))
          ≡⟨ cong (λ u → e-fib a₀ (∥-∥ₕ-elim {B = λ _ → fiber p a₀} (λ _ → fib-set a₀) (λ q → x , q ∙ r) u)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣) ⟩
            e-fib a₀ (x , refl ∙ r)
          ≡⟨⟩
            (∣ x ∣ , p x , refl) , refl ∙ r
          ≡⟨ ΣPathP (refl , lUnit r ⁻¹) ⟩
            (∣ x ∣ , p x , refl) , r
          ≡⟨ ΣPathP ((ΣPathP (refl , (ΣPathP (refl , ( transportIsoToPath⁻ (PathIdTruncIso 2) ∣ refl ∣ ⁻¹))))) , toPathP (transportRefl r)) ⟩
            (∣ x ∣ , p x , transport⁻ (PathIdTrunc 2) ∣ refl ∣) , r ∎
          ) q r
        ) (transport (PathIdTrunc 2) q))
    ) x q

  fibp≡fibp̃ : (a : ⟨ A ⟩) → fiber p a ≡ fiber p̃ a
  fibp≡fibp̃ a = isoToPath (iso (e-fib a) (e'-fib a) (λ x → e∘e' a (x .fst .snd .fst) (x .fst .fst) (x .fst .snd .snd) (x .snd)) λ x → e'∘e a (x .fst) (x .snd))

  X≡X̃ : X ≡ X̃
  X≡X̃ =
      X
    ≡⟨ ua (totalEquiv p) ⟩
      Σ ⟨ A ⟩ (fiber p)
    ≡⟨ Σ-cong-snd fibp≡fibp̃ ⟩
      Σ ⟨ A ⟩ (fiber p̃)
    ≡⟨ ua (totalEquiv p̃) ⁻¹ ⟩
      X̃ ∎


  transportX≡X̃ : (x : X) → transport X≡X̃ x ≡ e x
  transportX≡X̃ x =
      transport (ua (totalEquiv p) ∙ Σ-cong-snd fibp≡fibp̃ ∙ ua (totalEquiv p̃) ⁻¹ ∙ refl) x
    ≡⟨ transportComposite (ua (totalEquiv p)) (Σ-cong-snd fibp≡fibp̃ ∙ ua (totalEquiv p̃) ⁻¹ ∙ refl) x ⟩
      transport (Σ-cong-snd fibp≡fibp̃ ∙ ua (totalEquiv p̃) ⁻¹ ∙ refl) (transport (ua (totalEquiv p)) x)
    ≡⟨ transportComposite (Σ-cong-snd fibp≡fibp̃) (ua (totalEquiv p̃) ⁻¹ ∙ refl) (transport (ua (totalEquiv p)) x) ⟩
      transport (ua (totalEquiv p̃) ⁻¹ ∙ refl) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x))
    ≡⟨ transportComposite (ua (totalEquiv p̃) ⁻¹) refl (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x)) ⟩
      transport refl (transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x)))
    ≡⟨ transportRefl (transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x))) ⟩
      transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x))
    ≡⟨ cong (λ u → transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) u)) (uaβ (totalEquiv p) x) ⟩
      transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (p x , x , refl))
    ≡⟨ cong (transport (ua (totalEquiv p̃) ⁻¹)) (transportRefl (p x , (∣ x ∣ , p x , refl) , refl)) ⟩
      transport (ua (totalEquiv p̃) ⁻¹) (p x , (∣ x ∣ , p x , refl) , refl)
    ≡⟨ ~uaβ (totalEquiv p̃) (p x , (∣ x ∣ , p x , refl) , refl) ⟩
      e x ∎

  x≡x̃ : PathP (λ i → X≡X̃ i) x (∣ x ∣ , pt A , cong ∣_∣ p⋆)
  x≡x̃ = toPathP (
      transport X≡X̃ x
    ≡⟨ transportX≡X̃ x ⟩
      ∣ x ∣ , p x , cong ∣_∣ refl
    ≡⟨ ΣPathP (refl , (ΣPathP (p⋆ , (toPathP lemma)))) ⟩
      ∣ x ∣ , pt A , cong ∣_∣ p⋆ ∎)
    where

    lemma : subst (λ a → ∣ p x ∣ ≡ ∣ a ∣) p⋆ refl ≡ cong ∣_∣ p⋆
    lemma = substInPaths (λ _ → ∣ p x ∣) ∣_∣ p⋆ refl ∙ lUnit _ ⁻¹ ∙ lUnit _ ⁻¹

  p≡p̃ : PathP (λ i → X≡X̃ i → ⟨ A ⟩) p p̃
  p≡p̃ = symP (transport (cong (λ p → PathP (λ i → X≡X̃ (~ i) → ⟨ A ⟩) p̃ p) (funExt lemma)) (funTypeTransp (λ X → X) (λ _ → ⟨ A ⟩) (sym X≡X̃) p̃ ))
    where

    lemma : (x : X) → transport refl (p̃ (transport X≡X̃ x)) ≡ p x
    lemma x =
        transport refl (p̃ (transport X≡X̃ x))
      ≡⟨ transportRefl (p̃ (transport X≡X̃ x)) ⟩
        p̃ (transport X≡X̃ x)
      ≡⟨ cong p̃ (transportX≡X̃ x) ⟩
        p̃ (e x)
      ≡⟨⟩
        p x ∎

  p⋆≡refl : PathP (λ i → p≡p̃ i (x≡x̃ i) ≡ pt A) p⋆ refl
  p⋆≡refl = {!!}

  rightInv : SubGroupπ₁'→PCCovering₀' A conA (SubGroupπ₁'←PCCovering₀' A conA (((X , x) , p) , p⋆ , hypCon , fib-set)) ≡ (((X , x) , p) , p⋆ , hypCon , fib-set)
  rightInv = ΣPathP ((ΣPathP ((ΣPathP (X≡X̃ , x≡x̃)) , p≡p̃)) , (ΣPathP ({!!} , toPathP (isProp× isConnected'IsProp (isPropΠ (λ _ → isPropIsSet)) _ _)))) ⁻¹

{-
module GaloisCorrespondance (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) where

  galois-correspondance≅' : SubGroupπ₁' A ≅ PCCovering₀' A
  galois-correspondance≅' ._≅_.fun = SubGroupπ₁'→PCCovering₀' A conA
  galois-correspondance≅' ._≅_.inv = SubGroupπ₁'←PCCovering₀' A conA
  galois-correspondance≅' ._≅_.rightInv x = {!!}
  galois-correspondance≅' ._≅_.leftInv = {!!}

  galois-correspondance' : SubGroupπ₁' A ≃ PCCovering₀' A
  galois-correspondance' = isoToEquiv galois-correspondance≅'
-}
-}
