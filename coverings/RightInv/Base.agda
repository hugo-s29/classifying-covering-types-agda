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

  e∘e'-lemma : (x̃ : X̃) → (e (e' x̃) , e'-fib (p̃ x̃) (x̃ , refl) .snd) ≡ (x̃  , refl)
  e∘e'-lemma (∣x∣ , a , q) =
        ∥-∥ₕ-elim {B = λ ∣x∣ → (q : ∥p∥ ∣x∣ ≡ ∣ a ∣) → (e (e' (∣x∣ , a , q)) , e'-fib a ((∣x∣ , a , q) , refl) .snd) ≡ ((∣x∣ , a , q) , refl)}
            (λ ∣x∣ → isOfHLevelΠ 3 λ q → isSet→isGroupoid (isProp→isSet (fibp̃-isSet (p̃ (∣x∣ , a , q)) _ _)))
            (λ x q →
              subst (λ q → (e (e' (∣ x ∣ₕ , a , q)) , e'-fib a ((∣ x ∣ₕ , a , q) , refl) .snd) ≡ ((∣ x ∣ₕ , a , q) , refl)  ) (transport⁻Transport (PathIdTrunc 2) q) (
                ∥-∥ₕ-elim
                {B = λ q → (e (e' (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q)) , (e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q) , refl)) .snd) ≡ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q), refl)}
                (λ _ → isProp→isSet (fibp̃-isSet a _ _))
                (λ q →
                        e (e' (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣)) , e'-fib a ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl) .snd
                    ≡⟨⟩
                        e ( ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl)
                            (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ q ∣)) .fst) ,
                        ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ q → x , q ∙ refl)
                            (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ q ∣)) .snd
                    ≡⟨ cong {B = λ _ → fiber p̃ a}
                    (λ u → e (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                            (λ q → x , q ∙ refl) u .fst) ,
                                ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a)
                                (λ q → x , q ∙ refl) u .snd) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)
                    ⟩
                        e x , q ∙ refl
                    ≡⟨ cong {B = λ _ → fiber p̃ a} ( e x ,_ ) (rUnit q ⁻¹) ⟩
                        e x , q
                    ≡⟨ cong₃ {A = ⟨ A ⟩} {B = λ a → ∥p∥ ∣ x ∣ ≡ ∣ a ∣} {C = λ a' _ → a' ≡ a} {D = λ _ _ _ → fiber p̃ a}
                        (λ u v w → (∣ x ∣ , u , v) , w) q (λ i j → ∣ q (i ∧ j) ∣) (λ i j → q (i ∨ j))
                    ⟩
                        (∣ x ∣ , a , cong ∣_∣ q) , refl
                    ≡⟨ cong {A = ∣ p x ∣ ≡ ∣ a ∣} {B = λ _ → fiber p̃ a }
                        (λ u → (∣ x ∣ , a , u) , refl) (transportIsoToPath⁻ (PathIdTruncIso 2) ∣ q ∣ ⁻¹)
                    ⟩
                        (∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , refl ∎
                )
                (transport (PathIdTrunc 2) q))
            ) ∣x∣ q

  e∘e' : (x̃ : X̃) → e (e' x̃) ≡ x̃
  e∘e' x̃ = cong fst (e∘e'-lemma x̃)

  X≅X̃ : X ≅ X̃
  X≅X̃ = iso e e' e∘e' e'∘e

  X≡X̃ : X ≡ X̃
  X≡X̃ = isoToPath X≅X̃

  X̃≡X : X̃ ≡ X
  X̃≡X = X≡X̃ ⁻¹

  x̃ : X̃
  x̃ = ∣ x ∣ , pt A , cong ∣_∣ p⋆

  x̃≡tr-x̃ : PathP (λ i → X̃≡X i) x̃ (transport X̃≡X x̃)
  x̃≡tr-x̃ = transport-filler X̃≡X x̃

  tr-x̃≡e'x̃ : transport X̃≡X x̃ ≡ e' x̃
  tr-x̃≡e'x̃ = transportIsoToPath⁻ X≅X̃ x̃

  e'x̃≡x : e' x̃ ≡ x
  e'x̃≡x = refl

  x≡x̃ : PathP (λ i → X≡X̃ i) x x̃
  x≡x̃ = compPathP'
    {A = Type}
    {B = λ x → {!Type!}}
    {x' = x}
    {y' = transport X≡X̃ x}
    {z' = x̃}
    {p = X≡X̃}
    {q = refl}
    {!!}
    {!!}

  p̃≡tr∘p̃∘tr : PathP (λ i → X̃≡X i → ⟨ A ⟩) p̃ (transport refl ∘ p̃ ∘ transport X≡X̃)
  p̃≡tr∘p̃∘tr = funTypeTransp (λ X → X) (λ _ → ⟨ A ⟩) X̃≡X p̃

  tr∘p̃∘tr≡p̃∘e : transport refl ∘ p̃ ∘ transport X≡X̃ ≡ p̃ ∘ e
  tr∘p̃∘tr≡p̃∘e = funExt (λ x → transportRefl (p̃ (transport X≡X̃ x)) ∙ cong p̃ (transportIsoToPath X≅X̃ x))

  p̃∘e≡p : p̃ ∘ e ≡ p
  p̃∘e≡p = refl

  p≡p̃ : PathP (λ i → X≡X̃ i → ⟨ A ⟩) p p̃
  p≡p̃ = {!compPath!}

  p⋆≡refl : PathP (λ i → p≡p̃ i (x≡x̃ i) ≡ pt A) p⋆ refl
  p⋆≡refl = {!!}

