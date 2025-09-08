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

module CoveringToSubgroup (A : Pointed ℓ-zero) ((covering X p pt⋆ fib-set isCon) : Covering A) where
  Bi : (∥ ⟨ X ⟩ ∥ 3) → (∥ ⟨ A ⟩ ∥ 3)
  Bi = ∥-∥ₕ-map p

  --- F --> X --> ∥ X ∥
  --- | ⌟   |       |
  --- v     v       v
  --- 1 --> A --> ∥ A ∥

  fib-trunc-lemma : (a : ⟨ A ⟩) → fiber p a ≡ fiber Bi ∣ a ∣
  fib-trunc-lemma a = isoToPath (iso to of s r) where

    to : fiber p a → fiber Bi ∣ a ∣
    to (x , q) = ∣ x ∣ , (transport⁻ (PathIdTrunc 2) ∣ q ∣)

    of : fiber Bi ∣ a ∣ → fiber p a
    of (x , q) = ∥-∥ₕ-elim {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a} (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a)))
       (λ x → λ (q : ∣ p x ∣ ≡ ∣ a ∣) → ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) q)) x q

    s : section to of
    s (x , q) = ΣPathTransport→PathΣ (to (of (x , q))) (x , q) (l₁ x q , l₂) where

      arg₁ : (x : ∥ ⟨ X ⟩ ∥ 3) → Bi x ≡ ∣ a ∣ → ∥ ⟨ X ⟩ ∥ 3
      arg₁ x q = ∣ ∥-∥ₕ-elim {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a} (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a)))
       (λ x → λ (q : ∣ p x ∣ ≡ ∣ a ∣) → ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) q)) x q .fst ∣

      l₁' : (x : ⟨ X ⟩) (q : ∥ p x ≡ a ∥ 2) → Path (∥ ⟨ X ⟩ ∥ 3) ∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) q .fst ∣ ∣ x ∣
      l₁' x = ∥-∥ₕ-elim {B = λ q → Path (∥ ⟨ X ⟩ ∥ 3) ∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) q .fst ∣ ∣ x ∣}
              (λ q → subst⁻ isSet (PathIdTrunc 2) (isOfHLevelTrunc 2)) λ _ → refl

      l₁ : (x : ∥ ⟨ X ⟩ ∥ 3) (q : Bi x ≡ ∣ a ∣) → arg₁ x q ≡ x
      l₁ x q = ∥-∥ₕ-elim {B = λ x → ∀ q → arg₁ x q ≡ x}
        (λ x → isGroupoidΠ (λ q → isOfHLevelTruncPath {x = arg₁ x q} {y = x})) (λ x q → l₁' x (transport (PathIdTrunc 2) q)) x q

      arg₂ : (x : ∥ ⟨ X ⟩ ∥ 3) → Bi x ≡ ∣ a ∣ → Bi x ≡ ∣ a ∣
      arg₂ x q = subst (λ x → Bi x ≡ ∣ a ∣) (l₁ x q) (transport⁻ (PathIdTrunc 2) ∣ ∥-∥ₕ-elim {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a}
        (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a))) (λ x → λ (q : ∣ p x ∣ ≡ ∣ a ∣) → ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) q)) x q .snd ∣)

      l₂' : (x : ∥ ⟨ X ⟩ ∥ 3) (q : Bi x ≡ ∣ a ∣) → isGroupoid (arg₂ x q ≡ q)
      l₂' x q = isOfHLevelSuc 3 (isOfHLevelTruncPath {n = 3}) (arg₂ x q) q

      l₂'' : (x : ⟨ X ⟩) (q : ∥ p x ≡ a ∥ 2) → arg₂ ∣ x ∣ (transport⁻ (PathIdTrunc 2) q) ≡ (transport⁻ (PathIdTrunc 2) q)
      l₂'' x = ∥-∥ₕ-elim {B = λ q → arg₂ ∣ x ∣ (transport⁻ (PathIdTrunc 2) q) ≡ (transport⁻ (PathIdTrunc 2) q)} (λ _ → isOfHLevelTruncPath {n = 3} _ _) (λ q →
          subst (λ x → Bi x ≡ ∣ a ∣) (l₁ ∣ x ∣ (transport⁻ (PathIdTrunc 2) ∣ q ∣)) (transport⁻ (PathIdTrunc 2) (
            ∣
                (∥-∥ₕ-elim
                {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a}
                (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a)))
                (λ x q →
                   ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q)
                   (transport (PathIdTrunc 2) q))
                ∣ x ∣ (transport⁻ (PathIdTrunc 2) ∣ q ∣) .snd)
             ∣
            ))
        ≡⟨⟩
          subst (λ x → Bi x ≡ ∣ a ∣) (l₁' x (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ q ∣))) (transport⁻ (PathIdTrunc 2) (
            ∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ q ∣)) .snd ∣))
        ≡⟨ cong (λ u → subst (λ x → Bi x ≡ ∣ a ∣) (l₁' x u) (transport⁻ (PathIdTrunc 2) (∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) u .snd ∣))) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⟩
          subst (λ x → Bi x ≡ ∣ a ∣) (l₁' x ∣ q ∣) (transport⁻ (PathIdTrunc 2) ∣ q ∣)
        ≡⟨⟩
          subst {x = ∣ x ∣} (λ x → Bi x ≡ ∣ a ∣) refl (transport⁻ (PathIdTrunc 2) ∣ q ∣)
        ≡⟨ transportRefl (transport⁻ (PathIdTrunc 2) ∣ q ∣) ⟩
          transport⁻ (PathIdTrunc 2) ∣ q ∣ ∎
        )

      l₂ : arg₂ x q ≡ q
      l₂ = ∥-∥ₕ-elim {B = λ x → (q : Bi x ≡ ∣ a ∣) → arg₂ x q ≡ q} (λ x → isGroupoidΠ (l₂' x)) (λ x q →
          subst (λ q → arg₂ ∣ x ∣ q ≡ q) (transport⁻Transport (PathIdTrunc 2) q) (l₂'' x (transport (PathIdTrunc 2) q))
        ) x q

    r : retract to of
    r (x , q) = cong (∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)

  connected : isConnected' (∥ ⟨ X ⟩ ∥ 3)
  connected = ∣ ∣ pt X ∣ ∣₁ , ∥-∥ₕ-elim2 (λ _ _ → isSet→isGroupoid (isProp→isSet isPropPropTrunc)) λ a b → ∥-∥-elim (λ _ → isPropPropTrunc) (∣_∣₁ ∘ cong ∣_∣) (isCon .snd a b)

  isBi : (u : ∥ ⟨ A ⟩ ∥ 3) → isSet (fiber Bi u)
  isBi = ∥-∥ₕ-elim (λ _ → isSet→isGroupoid (isProp→isSet isPropIsSet)) λ a → subst isSet (fib-trunc-lemma a) (fib-set a)

  isGrp : isGroupoid (∥ ⟨ X ⟩ ∥ 3)
  isGrp = isOfHLevelTrunc 3

  subgrp : SubGroupπ₁ A
  subgrp = subgroup ((∥ ⟨ X ⟩ ∥ 3) , ∣ pt X ∣) Bi (cong ∣_∣ pt⋆) isBi connected isGrp
