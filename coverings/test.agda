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

{-
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

congP-compPathP :
  ∀ {ℓ ℓ'}
  (A : I → Type ℓ)
  {B_i1 : Type ℓ}
  (B : A i1 ≡ B_i1)
  (C : Type ℓ')
  {x : A i0}
  {y : A i1}
  {z : B i1}
  {f : A i0 → C}
  {g : A i1 → C}
  {h : B i1 → C}
  (p : PathP A x y)
  (q : PathP (λ i → B i) y z)
  (r : PathP (λ i → A i → C) f g)
  (s : PathP (λ i → B i → C) g h)
  →
  congP (λ i a → compPathP r s i {!!}) (compPathP p q) ≡ compPathP (congP {!!} p) (congP {!!} q)
congP-compPathP = {!!}

-}

compPathP'-refl-refl :
  ∀ {ℓ ℓ'}
  {A : Type ℓ}
  {B : A → Type ℓ'}
  {x : A}
  {x' : B x}
  →
  compPathP' {x = x} {B = B} {x' = x'} {p = refl} {q = refl} refl refl ≡ {!!}
compPathP'-refl-refl = {!!}


congP-compPathP' :
  ∀ {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  {B : A → Type ℓ'}
  {C : Type ℓ''}
  (x y : A)
  (p : x ≡ y)
  (x' : B x)
  (y' : B y)
  (P : PathP (λ i → B (p i)) x' y')
  (z : A)
  (q : y ≡ z)
  (z' : B z)
  (Q : PathP (λ i → B (q i)) y' z')
  (f : B x → C)
  (g : B y → C)
  (h : B z → C)
  (R : PathP (λ i → B (p i) → C) f g)
  (S : PathP (λ i → B (q i) → C) g h)
  →
  congP {B = λ _ _ → C} (λ i → compPathP' {B = λ a → B a → C} {p = p} {q = q} R S i) (compPathP' {B = B} {p = p} {q = q} P Q)
  ≡ compPathP' {p = p} {q = q} (congP (λ i → R i) P) (congP (λ i → S i) Q)
congP-compPathP' {A = A} {B = B} {C = C} x y p x' y' = JDep {B = B} (λ y p y' P →
    (z : A)
    (q : y ≡ z)
    (z' : B z)
    (Q : PathP (λ i → B (q i)) y' z')
    (f : B x → C)
    (g : B y → C)
    (h : B z → C)
    (R : PathP (λ i → B (p i) → C) f g)
    (S : PathP (λ i → B (q i) → C) g h)
    →
    congP {B = λ _ _ → C} (λ i → compPathP' {B = λ a → B a → C} {p = p} {q = q} R S i) (compPathP' {B = B} {p = p} {q = q} P Q)
    ≡ compPathP' {p = p} {q = q} (congP (λ i → R i) P) (congP (λ i → S i) Q)
  ) (λ z q z' → JDep {B = B} (λ z q z' Q →
    (f g : B x → C)
    (h : B z → C)
    (R : PathP (λ i → B x → C) f g)
    (S : PathP (λ i → B (q i) → C) g h)
    →
    congP {B = λ _ _ → C} (λ i → compPathP' {B = λ a → B a → C} {q = q} R S i) (compPathP' {B = B} {q = q} refl Q)
    ≡ compPathP' {p = refl} {q = q} (congP (λ i → R i) refl) (congP (λ i → S i) Q)
  ) (λ f g h R S →
    congP (λ i → compPathP' {B = λ a → B a → C} R S i) (compPathP' {B = B} {x' = x'} refl refl)
    ≡⟨ {!!} ⟩
    congP (λ i → compPathP' {B = λ a → B a → C} R S i) ? -- j'ai envie de mettre refl_x' ici, mais ça ne type pas car refl ∙ refl n'est pas définitionnellement égal à refl
    ≡⟨ {!!} ⟩
    compPathP' {p = refl {x = x}} {q = refl} (λ i → R i x') (λ i → S i x') ∎
    ) q) p
