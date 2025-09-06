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
import SubgroupToCovering
import CoveringToSubgroup

module RightInv.Base (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where

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
  fibp̃-isSet a = SubgroupToCovering.p-isCov₀ A (∥ X , x ∥∙ 3) conA (CoveringToSubgroup.connected A (((X , x) , p) , p⋆ , hypCon , fib-set)) (CoveringToSubgroup.Bi∙ A (((X , x) , p) , (p⋆ , hypCon , fib-set))) a
{-
  e∘e'-mini-lemma₁ : (x : X) (a : ⟨ A ⟩) (q :  p x ≡ a) → e (e' (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣)) ≡ (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣)
  e∘e'-mini-lemma₁ x a q =
      e (e' (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣))
    ≡⟨ cong (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⟩
      ∣ x ∣ , p x , refl
    ≡⟨ cong₂ {C = λ _ _ → X̃} (λ u v → ∣ x ∣ , u , v) q (λ i j → ∣ q (i ∧ j) ∣) ⟩
      ∣ x ∣ , a , cong ∣_∣ q
    ≡⟨ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹ ⟩
      ∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣ ∎

  e∘e'-mini-lemma₂ : (x : X) (a : ⟨ A ⟩) (q : p x ≡ a) → PathP (λ i → p̃ (e∘e'-mini-lemma₁ x a q i) ≡ a) (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd) refl
  e∘e'-mini-lemma₂ x a q = toPathP lem
    where

    lem : subst (λ x → p̃ x ≡ a) (e∘e'-mini-lemma₁ x a q) (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd) ≡ refl
    lem =
        subst (λ x → p̃ x ≡ a) (
          cong (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
          ∙ cong₂ {C = λ _ _ → X̃} (λ u v → ∣ x ∣ , u , v) q (λ i j → ∣ q (i ∧ j) ∣)
          ∙ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹
          ∙ refl
        ) (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd)
      ≡⟨ substInPaths p̃ (λ _ → a) (
          cong (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
          ∙ cong₂ {C = λ _ _ → X̃} (λ u v → ∣ x ∣ , u , v) q (λ i j → ∣ q (i ∧ j) ∣)
          ∙ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹
          ∙ refl
        ) (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd) ⟩
        cong p̃ (
          cong (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
          ∙ cong₂ {C = λ _ _ → X̃} (λ u v → ∣ x ∣ , u , v) q (λ i j → ∣ q (i ∧ j) ∣)
          ∙ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹
          ∙ refl
        ) ⁻¹
        ∙ (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd)
        ∙ refl
      ≡⟨ cong (λ u → cong p̃ u ∙ (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd) ∙ refl) (lem₀
        (cong (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣))
        (cong₂ {C = λ _ _ → X̃} (λ u v → ∣ x ∣ , u , v) q (λ i j → ∣ q (i ∧ j) ∣))
        (cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) ⁻¹)
        refl
      )⟩
        cong p̃ (
          refl
          ∙ cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣)
          ∙ cong₂ {C = λ _ _ → X̃} (λ u v → ∣ x ∣ , u , v) q (λ i j → ∣ q (i ∧ j) ∣) ⁻¹
          ∙ cong (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⁻¹
        )
        ∙ (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd)
        ∙ refl
      ≡⟨ cong (λ u → u ∙ e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd ∙ refl) (
        lem₁ p̃
        refl
        (cong {B = λ _ → X̃} (λ u → ∣ x ∣ , a , u) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣))
        (cong₂ {C = λ _ _ → X̃} (λ u v → ∣ x ∣ , u , v) q (λ i j → ∣ q (i ∧ j) ∣) ⁻¹)
        (cong (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⁻¹)
      )⟩
        (refl
        ∙ refl -- cong (λ u → a) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣) -- refl
        ∙ q ⁻¹ -- cong₂ (λ u v → p̃ {!u!}) q (λ i j → ∣ q (i ∧ j) ∣) ⁻¹ -- = q ⁻¹
        ∙ cong (λ u → p (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⁻¹)
        ∙ (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ q ∣)) .snd)
        ∙ refl
      ≡⟨ {!!} ⟩
        (refl
        ∙ refl
        ∙ q ⁻¹
        ∙ cong (λ u → p (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl) u .fst)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⁻¹)
        ∙ (q ∙ refl)
        ∙ refl
      ≡⟨ {!!} ⟩
        (refl ∙ refl ∙ q ⁻¹ ∙ refl) -- cong (λ _ → x) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⁻¹)
        ∙ (q ∙ refl) ∙ refl
      ≡⟨ {!!} ⟩
        refl ∎

      where

        lem₀ :
          {A : Type}
          {a b c d e : A}
          (p : a ≡ b)
          (q : b ≡ c)
          (r : c ≡ d)
          (s : d ≡ e)
          → (p ∙ q ∙ r ∙ s) ⁻¹ ≡ s ⁻¹ ∙ r ⁻¹ ∙ q ⁻¹ ∙ p ⁻¹
        lem₀ p q r s =
            (p ∙ q ∙ r ∙ s) ⁻¹
          ≡⟨ sym-conc p (q ∙ r ∙ s) ⟩
            (q ∙ r ∙ s) ⁻¹ ∙ p ⁻¹
          ≡⟨ cong (_∙ p ⁻¹) (sym-conc q (r ∙ s)) ⟩
            ((r ∙ s) ⁻¹ ∙ q ⁻¹) ∙ p ⁻¹
          ≡⟨ assoc _ _ _ ⁻¹ ⟩
            (r ∙ s) ⁻¹ ∙ q ⁻¹ ∙ p ⁻¹
          ≡⟨ cong (λ u → u ∙ q ⁻¹ ∙ p ⁻¹) (sym-conc r s) ⟩
            (s ⁻¹ ∙ r ⁻¹) ∙ q ⁻¹ ∙ p ⁻¹
          ≡⟨ assoc _ _ _ ⁻¹ ⟩
             s ⁻¹ ∙ r ⁻¹ ∙ q ⁻¹ ∙ p ⁻¹ ∎

        lem₁ :
            {A B : Type}
            {a b c d e : A}
            (f : A → B)
            (p : a ≡ b)
            (q : b ≡ c)
            (r : c ≡ d)
            (s : d ≡ e)
            → cong f (p ∙ q ∙ r ∙ s) ≡ cong f p ∙ cong f q ∙ cong f r ∙ cong f s
        lem₁ f p q r s =
          cong f (p ∙ q ∙ r ∙ s)
          ≡⟨ cong∙ f p (q ∙ r ∙ s) ⟩
          cong f p ∙ cong f (q ∙ r ∙ s)
          ≡⟨ cong (cong f p ∙_) (cong∙ f q (r ∙ s)) ⟩
          cong f p ∙ cong f q ∙ cong f (r ∙ s)
          ≡⟨ cong (λ u → cong f p ∙ cong f q ∙ u) (cong∙ f r s) ⟩
          cong f p ∙ cong f q ∙ cong f r ∙ cong f s ∎
-}
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
  x̃ = ∣ x ∣ , pt A , cong ∣_∣ p⋆

  x̃≡tr-x̃ : PathP (λ i → X̃≡X i) x̃ (transport X̃≡X x̃)
  x̃≡tr-x̃ = transport-filler X̃≡X x̃

  tr-x̃≡e'x̃ : transport X̃≡X x̃ ≡ e' x̃
  tr-x̃≡e'x̃ = uaβ X̃≃X x̃

  e'x̃≡x : e' x̃ ≡ x
  e'x̃≡x = refl

  x≡x̃∙ : PathP (λ i → (X̃≡X ∙ refl) i) x̃ x
  x≡x̃∙ = compPathP'
    {A = Type}
    {B = λ x → x}
    {x' = x̃}
    {y' = transport X̃≡X x̃}
    {z' = x}
    {p = X̃≡X}
    {q = refl}
    x̃≡tr-x̃
    tr-x̃≡e'x̃

  x≡x̃ : PathP (λ i → X̃≡X i) x̃ x
  x≡x̃ = subst⁻ (λ u → PathP (λ i → u i) x̃ x) (rUnit X̃≡X) x≡x̃∙

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

{-
  p⋆≡refl : PathP (λ i → p≡p̃ i (x≡x̃ i) ≡ pt A) p⋆ refl
  p⋆≡refl = {!!}

-}
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
