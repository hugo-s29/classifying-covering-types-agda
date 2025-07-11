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

congP-funTypeTransp : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} (B : A → Type ℓ')
  (C : A → Type ℓ'') {x y : A} (p : x ≡ y) (f : B x → C x) (g : B y → C y)
  {u : B x} {v : B y}
  (q : PathP (λ i → B (p i)) u v)
  (r : subst C p ∘ f ∘ subst B (sym p) ≡ g)
  →
  congP (λ i → subst (PathP (λ i → B (p i) → C (p i)) f) r (funTypeTransp B C p f) i) q
  ≡ compPathP' (congP {!!} q) (toPathP ?)
congP-funTypeTransp = {!!}
