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
open import SubgroupToCovering
open import CoveringToSubgroup

module _ (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) where
  SubGroupπ₁'→PCCovering₀' : SubGroupπ₁' A → PCCovering₀' A
  SubGroupπ₁'→PCCovering₀' ((X , Bi) , Bi-⋆ , conX , _ , Bi-set) = Subgroup→PCCovering₀.connectedCovering₀ A X conA conX (Bi , Bi-set , Bi-⋆)

  SubGroupπ₁'←PCCovering₀' : PCCovering₀' A → SubGroupπ₁' A
  SubGroupπ₁'←PCCovering₀' = PCCovering₀→Subgroup.subgroup A

is-1-connected-iso : {A B : Type} (f : A → B) → isConnectedFun 3 f → (∥ A ∥ 3) ≅ (∥ B ∥ 3)
is-1-connected-iso f h ._≅_.fun = ∥-∥ₕ-map f
is-1-connected-iso f h ._≅_.inv = ∥-∥ₕ-elim (λ _ → isOfHLevelTrunc 3) λ b → ∥-∥ₕ-map fst (h b .fst)
is-1-connected-iso {B = B} f h ._≅_.rightInv = ∥-∥ₕ-elim (λ x → isOfHLevelTruncPath {y = x}) lemma where
  lemma : (b : B) → ∥-∥ₕ-map f (∥-∥ₕ-map fst (h b .fst)) ≡ ∣ b ∣
  lemma b = ∥-∥ₕ-elim (λ x → isOfHLevelTruncPath {x = ∥-∥ₕ-map f (∥-∥ₕ-map fst x)}) (λ (_ , p) → cong ∣_∣ p) (h b .fst)
is-1-connected-iso {A = A} f h ._≅_.leftInv = ∥-∥ₕ-elim (λ x → isOfHLevelTruncPath {y = x}) lemma where
  lemma : (a : A) → ∥-∥ₕ-map fst (h (f a) .fst) ≡ ∣ a ∣
  lemma a = cong (∥-∥ₕ-map fst) (h (f a) .snd ∣ a , refl ∣)

is-1-connected-equiv : {A B : Type} (f : A → B) → isConnectedFun 3 f → (∥ A ∥ 3) ≃ (∥ B ∥ 3)
is-1-connected-equiv f h = isoToEquiv (is-1-connected-iso f h)

transport-fun : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'} (p : A ≡ B) (f : A → C) (g : B → C) → (∀ x → f x ≡ g (transport p x)) → subst (λ A' → A' → C) p f ≡ g
transport-fun {B = B} {C = C} p f =
  J (λ B p → (g : B → C) → (∀ x → f x ≡ g (transport p x)) → subst (λ X → X → C) p f ≡ g )
  (λ g h → transportRefl f ∙ funExt (λ x → (h x) ∙ (cong g (transportRefl x)))) p

transport-fun⁻ : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'} (p : A ≡ B) (f : A → C) (g : B → C) → subst (λ A' → A' → C) p f ≡ g → ∀ x → f x ≡ g (transport p x)
transport-fun⁻ {B = B} {C = C} p f =
  J (λ B p → (g : B → C) → subst (λ X → X → C) p f ≡ g → ∀ x → f x ≡ g (transport p x))
  (λ g u x → funExt⁻ (substRefl {B = λ X → X → C} f ⁻¹ ∙ u) x ∙ cong g (transportRefl x ⁻¹)) p

transport-Σ : ∀ {A : Type} {B C : A → Type} (x : Σ A B) (p : (a : A) → B a ≡ C a) → transport (λ i → Σ A (λ a → p a i)) x ≡ (fst x , transport (p (fst x)) (snd x))
transport-Σ {A = A} x@(a , b) p = fromPathP lem
  where
  lem : PathP (λ i → Σ A (λ a → p a i)) x (fst x , transport (p (fst x)) (snd x))
  lem = ΣPathP (refl , (transport-filler (p a) b))
