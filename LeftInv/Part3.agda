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

module LeftInv.Part3 (A : Pointed ℓ-zero) ((subgroup BG Bi Bi-⋆ isBi isCon grpBG) : SubGroupπ₁ A) where
  open import LeftInv.Base A (subgroup BG Bi Bi-⋆ isBi isCon grpBG)


  abstract
    congP3 : congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣ ≡ cong Bi (s∘t (pt BG) ) ∙ Bi-⋆
    congP3 =
        congP (λ i → Bi∘s≡∥p∥ i) (cong₂ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣)) Bi-⋆ (λ i j → Bi-⋆ (i ∧ j)))
      ≡⟨⟩
        congP₂ {B = λ _ a → Bi (pt BG) ≡ a} {C = λ _ _ _ → ∥ ⟨ A ⟩ ∥ 3} (λ i a b → ∥-∥ₕ-elim {B = λ x → Bi (s x) ≡ ∥p∥ x} (λ x → isOfHLevelTruncPath {y = ∥p∥ x}) (λ (_ , _ , q) → q) (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) a b) i) Bi-⋆ (λ i j → Bi-⋆ (i ∧ j))
      ≡⟨ cong (λ x → congP₂ {B = λ _ a → Bi (pt BG) ≡ a} {C = λ _ _ _ → ∥ ⟨ A ⟩ ∥ 3} (λ i a b → x a b i) Bi-⋆ (λ i j → Bi-⋆ (i ∧ j))) lem₀ ⟩
        congP
        (λ i b →
            ∥-∥ₕ-elim
            {B =
            λ a →
              (b : Bi (pt BG) ≡ a) →
              Bi
              (s
                (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
                (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
                (λ a' b' → ∣ pt BG , a' , b' ∣) a b))
              ≡
              ∥p∥
              (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
                (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
                (λ a' b' → ∣ pt BG , a' , b' ∣) a b)}
            (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
            (λ a b → b) (Bi-⋆ i) b i)
          (λ i j → Bi-⋆ (i ∧ j))
      ≡⟨⟩
        (λ i →
          ∥-∥ₕ-elim
          {B =
            λ a →
              (b : Bi (pt BG) ≡ a) →
              Bi
              (s
              (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
                (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
                (λ a' b' → ∣ pt BG , a' , b' ∣) a b))
              ≡
              ∥p∥
              (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
              (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
              (λ a' b' → ∣ pt BG , a' , b' ∣) a b)}
          (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
          (λ a b → b) (Bi-⋆ i) (λ j → Bi-⋆ (i ∧ j))
          i
        )
      ≡⟨ cong₂
          {A = (a : ∥ ⟨ A ⟩ ∥ 3) (b : Bi (pt BG) ≡ a) → ∥ ⟨ A ⟩ ∥ 3}
          {B = λ u → (a : ⟨ A ⟩) (b : Bi (pt BG) ≡ ∣ a ∣) → Bi (s (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ z → isGroupoidΠ (λ _ → isOfHLevelTrunc 3)) (λ a' b' → ∣ pt BG , a' , b' ∣) ∣ a ∣ b)) ≡ u ∣ a ∣ b}
          {C = λ u v → Bi (s ∣x∣') ≡ u ∣ pt A ∣ Bi-⋆}
          (λ x y i →
              ∥-∥ₕ-elim
              {B =
                λ a →
                  (b : Bi (pt BG) ≡ a) →
                  Bi
                  (s
                  (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
                    (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
                    (λ a' b' → ∣ pt BG , a' , b' ∣) a b))
                  ≡
                  x a b}
              (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
              (λ a b → y a b) (Bi-⋆ i) (λ j → Bi-⋆ (i ∧ j))
              i
            )
          (λ i a b → lem₁ a b i)
          refl
      ⟩
        (λ i →
          ∥-∥ₕ-elim
          {B =
            λ a →
              (b : Bi (pt BG) ≡ a) →
              Bi
              (s
              (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
                (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
                (λ a' b' → ∣ pt BG , a' , b' ∣) a b))
              ≡ a}
          (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
          (λ a b → b) (Bi-⋆ i) (λ j → Bi-⋆ (i ∧ j))
          i
        )
      ≡⟨ lem₂ ⟩
        cong Bi (s∘t (pt BG)) ∙ Bi-⋆ ∎ where


      lem₀ : (λ (a : ∥ ⟨ A ⟩ ∥ 3) (b : Bi (pt BG) ≡ a) → ∥-∥ₕ-elim
            {B = λ x → Bi (s x) ≡ ∥p∥ x}
            (λ x → isOfHLevelTruncPath {y = ∥p∥ x})
            (λ (_ , _ , q) → q)
            (∥-∥ₕ-elim
              {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
              (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3)
              (λ a r → ∣ pt BG , a , r ∣)
              a b))
          ≡ ∥-∥ₕ-elim
            {B = λ a → (b : Bi (pt BG) ≡ a) →
              Bi (s (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3)) (λ a' b' → ∣ pt BG , a' , b' ∣) a b))
              ≡ ∥p∥ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3)) (λ a' b' → ∣ pt BG , a' , b' ∣) a b)   }
            (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
            (λ a b → b)
      lem₀ = funExt (λ a → funExt (λ b → ∘-∥-∥ₕ-3-elim (λ ((_ , _ , q)) → q) (λ a b → pt BG , a , b) a b))

      lem₁ : (a : ∥ ⟨ A ⟩ ∥ 3) (b : Bi (pt BG) ≡ a) → ∥p∥ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3)) (λ a' b' → ∣ pt BG , a' , b' ∣) a b) ≡ a
      lem₁ = ∥-∥ₕ-elim
        {B = λ a → (b : Bi (pt BG) ≡ a) → ∥p∥ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3)) (λ a' b' → ∣ pt BG , a' , b' ∣) a b) ≡ a}
        (λ a → isGroupoidΠ λ _ → isOfHLevelTruncPath {y = a})
        λ _ _ → refl

      lem₂ :
          (λ i →
            ∥-∥ₕ-elim
            {B =
              λ a →
                (b : Bi (pt BG) ≡ a) →
                Bi
                (s
                (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
                  (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
                  (λ a' b' → ∣ pt BG , a' , b' ∣) a b))
                ≡
                a}
            (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
            (λ a b → b) (Bi-⋆ i) (λ j → Bi-⋆ (i ∧ j))
            i
          )
          ≡ cong Bi (s∘t (pt BG)) ∙ Bi-⋆
      lem₂ = J (λ a Bi-⋆ →
          (λ i →
            ∥-∥ₕ-elim
            {B =
              λ a →
                (b : Bi (pt BG) ≡ a) →
                Bi
                (s
                (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
                  (λ _ → isGroupoidΠ (λ _ → isOfHLevelTrunc 3))
                  (λ a' b' → ∣ pt BG , a' , b' ∣) a b))
                ≡
                a
                }
            (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
            (λ a b → b) (Bi-⋆ i) (λ j → Bi-⋆ (i ∧ j))
            i
          )
          ≡ cong Bi (s∘t (pt BG)) ∙ Bi-⋆
        ) (
          ∥-∥ₕ-elim
          {B = λ a → (r : Bi (pt BG) ≡ a) → Bi (s (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) a r)) ≡ a}
          (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
          (λ _ b → b)
          (Bi (pt BG))
          refl
        ≡⟨
          cong₂
              {A = (a : ∥ ⟨ A ⟩ ∥ 3) → Bi (pt BG) ≡ a → ∥ ⟨ A ⟩ ∥ 3}
              {B = λ u → (a : ⟨ A ⟩) (r : Bi (pt BG) ≡ ∣ a ∣) → Bi (pt BG) ≡ u ∣ a ∣ r}
              (λ u v →
              ∥-∥ₕ-elim
                  {B = λ a → (r : Bi (pt BG) ≡ a) → Bi (s (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) a r)) ≡ u a r}
                  (λ a → isOfHLevelΠ 3 (λ b → isOfHLevelTruncPath {n = 3}))
                  v
                  (Bi (pt BG))
                  refl
              ) (funExt (λ _ → funExt sym)) (symP (λ i _ r j → r (i ∧ j)))
        ⟩
          ∥-∥ₕ-elim
          {B = λ a → (r : Bi (pt BG) ≡ a) → Bi (s (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) a r)) ≡ Bi (pt BG)}
          (λ _ → isOfHLevelΠ 3 (λ _ → isOfHLevelTruncPath {n = 3}))
          (λ _ _ → refl)
          (Bi (pt BG))
          refl
        ≡⟨ ∥-∥ₕ-elim-cong Bi (λ a r → s (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) a r)) (λ _ _ → pt BG) (λ _ _ → refl) (Bi (pt BG)) refl {r = isOfHLevelTrunc 3} ⁻¹ ⟩
          cong Bi (
            ∥-∥ₕ-elim
            {B = λ a → (r : Bi (pt BG) ≡ a) → s (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) a r) ≡ pt BG}
            (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (grpBG _ _))
            (λ _ _ → refl)
            (Bi (pt BG))
            refl
          )
        ≡⟨ rUnit (cong Bi (s∘t (pt BG))) ⟩
          cong Bi (s∘t (pt BG)) ∙ refl ∎
        ) Bi-⋆
