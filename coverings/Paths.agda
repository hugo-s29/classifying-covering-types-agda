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

J2Dep : {ℓ ℓ' ℓ'' ℓ''' : Level}
    {A : Type ℓ}
    {B : A → Type ℓ'}
    {C : (a : A) → B a → Type ℓ''}
    {x : A}
    {b : B x}
    {c : C x b}
    (P : (y : A) (p : x ≡ y) (z : B y) (q : PathP (λ i → B (p i)) b z) (u : C y z) (r : PathP (λ i → C (p i) (q i)) c u) → Type ℓ''')
    (d : P _ refl _ refl _ refl)
    {y : A} (p : x ≡ y) {z : B y} (q : PathP (λ i → B (p i)) b z) {u : C y z} (r : PathP (λ i → C (p i) (q i)) c u) → P _ p _ q _ r
J2Dep {A = A} {x = x} P d p q r = transport (λ i → P _ _ _ (λ j → q (i ∧ j)) _ (λ j → r (i ∧ j))) d


compPathP'-nondep : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {u v w : A} {r : u ≡ v} {s : v ≡ w} {a b c : B} (p : a ≡ b) (q : b ≡ c) →
  compPathP' {B = λ _ → B} {p = r} {q = s} p q ≡ p ∙ q
compPathP'-nondep {B = B} {r = r} {s = s} p = J
  (λ c q → compPathP' {B = λ _ → B} {p = r} {q = s} p q ≡ p ∙ q)
  (
    compPathP' {B = λ _ → B} {p = r} {q = s} p refl
  ≡⟨ rUnitP' (λ _ → B) {p = r} p ⁻¹ ⟩
    p
  ≡⟨ rUnit p ⟩
    p ∙ refl ∎
  )

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
congP-compPathP' {A = A} {B = B} {C = C} x y p x' y' P z q z' Q f g h R S =
  J2Dep {B = B} {C = λ a _ → B a → C} (λ y p y' P g R →
    (z : A)
    (q : y ≡ z)
    (z' : B z)
    (Q : PathP (λ i → B (q i)) y' z')
    (h : B z → C)
    (S : PathP (λ i → B (q i) → C) g h)
    →
    congP {B = λ _ _ → C} (λ i → compPathP' {B = λ a → B a → C} {p = p} {q = q} R S i) (compPathP' {B = B} {p = p} {q = q} P Q)
    ≡ compPathP' {p = p} {q = q} (congP (λ i → R i) P) (congP (λ i → S i) Q)
  )
  (λ z q z' Q h S →
    J2Dep {B = B} {C = λ a _ → B a → C} (λ z q z' Q h S →
      congP {B = λ _ _ → C} (λ i → compPathP' {B = λ a → B a → C} {p = refl} {q = q} refl S i) (compPathP' {B = B} {p = refl} {q = q} refl Q)
      ≡ compPathP' {p = refl} {q = q} refl (congP (λ i → S i) Q)
    ) (lemma₁ ∙ lemma₂) q Q S
  ) p P R z q z' Q h S where

  lemma₁ : congP {B = λ _ _ → C} (λ i → compPathP' {B = λ a → B a → C} {q = refl} (refl {x = f}) refl i) (compPathP' {B = B} refl refl) ≡ (congP (λ _ → f) refl)
  lemma₁ =
    congP₂
    {A = λ j → PathP (λ i → B ((compPathRefl {x = x}) j i)) x' x'}
    {B = λ j _ → PathP (λ i → B ((compPathRefl {x = x}) j i) → C) f f}
    {C = λ _ _ _ → f x' ≡ f x'}
    (λ _ a b → congP (λ i → b i) a)
    {x = refl}
    {y = compPathP' {B = B} refl refl}
    {u = refl}
    {v = compPathP' {B = λ a → B a → C} refl refl}
    (rUnitP' B refl)
    (rUnitP' (λ a → B a → C) refl) ⁻¹

  lemma₂ : refl ≡ compPathP' {B = λ _ → C} {p = refl {x = x'}} {q = refl {x = x'}} (refl {x = f x'}) refl
  lemma₂ = rUnitP' (λ _ → C) {p = refl {x = x'}} refl


∘-∥-∥ₕ-3-elim :
  ∀ {ℓ ℓ' ℓ'' ℓ'''}
  {A : Type ℓ}
  {B : ∥ A ∥ 3 → Type ℓ'}
  {C : Type ℓ''}
  {D : ∥ C ∥ 3 → Type ℓ'''}
  {p : (x : ∥ A ∥ 3) → isOfHLevel 3 (B x → ∥ C ∥ 3)}
  {q : (x : ∥ C ∥ 3) → isOfHLevel 3 (D x)}
  (f : (c : C) → D ∣ c ∣ₕ)
  (g : (a' : A) (b' : B ∣ a' ∣ₕ) → C)
  (a : ∥ A ∥ 3)
  (b : B a)
  →
  ∥-∥ₕ-elim {B = λ c → D c} q f (∥-∥ₕ-elim {B = λ a → B a → ∥ C ∥ 3} p (λ a' b' → ∣ g a' b' ∣ₕ) a b)
  ≡ ∥-∥ₕ-elim {B = λ a → (b : B a) → D (∥-∥ₕ-elim {B = λ a → B a → ∥ C ∥ 3} p (λ a' b' → ∣ g a' b' ∣ₕ) a b)} (λ a → isOfHLevelΠ 3 (λ b → q _)) (λ a' b' → f (g a' b')) a b
∘-∥-∥ₕ-3-elim {q = q} f g = ∥-∥ₕ-elim (λ a → isOfHLevelΠ 3 (λ b → isSet→isGroupoid (q _ _ _))) λ _ _ → refl

∥-∥ₕ-elim-cong :
  {A C D : Type}
  {B : ∥ A ∥ 3 → Type}
  (f : C → D)
  (h k : (a : ∥ A ∥ 3) → B a → C)
  (g : (a : A) → (b : B ∣ a ∣) → (h ∣ a ∣ b) ≡ (k ∣ a ∣ b))
  (a : ∥ A ∥ 3)
  (b : B a)
  {p : (x : ∥ A ∥ 3) → isGroupoid ((b : B x) → h x b ≡ k x b)}
  {q : (x : ∥ A ∥ 3) → isGroupoid ((b : B x) → f (h x b) ≡ f (k x b))}
  {r : isGroupoid D}
  →
  cong f (∥-∥ₕ-elim {B = λ x → (b : B x) → h x b ≡ k x b} p g a b)
  ≡ ∥-∥ₕ-elim {B = λ a → (b : B a) → f (h a b) ≡ f (k a b)} q (λ a b → cong f (g a b)) a b
∥-∥ₕ-elim-cong {B = B} f h k g a b {p = p} {q = q} {r = r} = ∥-∥ₕ-elim
  {B = λ a → (b : B a) →
    cong f (∥-∥ₕ-elim {B = λ x → (b : B x) → h x b ≡ k x b} p g a b)
    ≡ ∥-∥ₕ-elim {B = λ a → (b : B a) → f (h a b) ≡ f (k a b)} q (λ a b → cong f (g a b)) a b
  }
  (λ a → isGroupoidΠ λ b → isOfHLevelPath 3 (isOfHLevelPath 3 r (f (h a b)) (f (k a b))) _ _) (λ _ _ → refl) a b
