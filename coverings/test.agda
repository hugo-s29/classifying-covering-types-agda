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
congP-funTypeTransp : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} (B : A → Type ℓ')
  (C : A → Type ℓ'') {x y : A} (p : x ≡ y) (f : B x → C x) (g : B y → C y)
  {u : B x} {v : B y}
  (q : PathP (λ i → B (p i)) u v)
  (r : subst C p ∘ f ∘ subst B (sym p) ≡ g)
  →
  congP (λ i → subst (PathP (λ i → B (p i) → C (p i)) f) r (funTypeTransp B C p f) i) q
  ≡ compPathP' (congP {!!} q) (toPathP {!!})
congP-funTypeTransp = {!!}
-}


{-
magic :
  (A : Type)
  (B : A → Type)
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  {u : B x}
  {v : B y}
  {w : B z}
  (P : PathP (λ i → B (p i)) u v)
  (Q : PathP (λ i → B (q i)) v w)
  (h : transport (λ i → B ((p ∙ q) i)) u ≡ w)
  →
  compPathP' {B = B} {p = p} {q = q} P Q ≡ subst (PathP (λ i → B ((p ∙ q) i)) u) h (transport-filler (λ i → B ((p ∙ q) i)) u)
magic A B {x = x} p q {u = u} P Q h = JDep
  (λ z q w Q → (h : transport (λ i → B ((p ∙ q) i)) u ≡ w) → compPathP' {B = B} {p = p} {q = q} P Q ≡ subst (PathP (λ i → B ((p ∙ q) i)) u) h (transport-filler (λ i → B ((p ∙ q) i)) u))
  (JDep (λ y p v P → (h : transport (λ i → B ((p ∙ refl) i)) u ≡ v) → compPathP' {B = B} {p = p} {q = refl} P refl ≡ subst (PathP (λ i → B ((p ∙ refl) i)) u) h (transport-filler (λ i → B ((p ∙ refl) i)) u))
  (λ h →
    compPathP' lemma₃ (compPathP' lemma₂ (lemma₁ h))
    ) p P
  ) q Q h where


  lemma₁ : (h : transport (λ i → B ((refl ∙ (λ _ → x)) i)) u ≡ u) → PathP (λ i → PathP (λ j → B (rUnit {x = x} refl i j)) u u) (subst (PathP (λ i → B x) u) (transportRefl u) (transport-filler (λ i → B x) u)) (subst (PathP (λ i → B ((refl ∙ (λ _ → x)) i)) u) h (transport-filler (λ i → B ((refl ∙ (λ _ → x)) i)) u))
  lemma₁ h = {!!}

  lemma₂ : refl ≡ subst (PathP (λ i → B x) u) (transportRefl u) (transport-filler (λ i → B x) u)
  lemma₂ = {!!}

  lemma₃ : PathP (λ i → PathP (λ j → B (rUnit refl (~ i) j)) u u) (compPathP' refl (λ _ → u)) refl
  lemma₃ = symP (rUnitP' B refl)


-}


funTypeTransp-congP :
  {A B C : Type}
  {x : A} {y : B}
  (p : A ≡ B)
  (P : PathP (λ i → p i) x (transport p x))
  (f : A → C)
  (g : B → C)
  (l : (y : B) → transport refl (f (transport⁻ p y)) ≡ g y)
  →
  congP (λ i → subst (PathP (λ i → p i → C) f) (funExt l) (funTypeTransp (λ X → X) (λ _ → C) p f) i) P
  ≡
  cong f (transport⁻Transport p x) ⁻¹ ∙ transportRefl _ ⁻¹ ∙ l (transport p x)
funTypeTransp-congP {A = A} {C = C} {x = x} p P = {!!}

{- JDep (λ B p y P →
    (q : transport p x ≡ y)
    (f : A → C)
    (g : B → C)
    (l : (y : B) → transport refl (f (transport⁻ p y)) ≡ g y)
    →
    congP (λ i → subst (PathP (λ i → p i → C) f) (funExt l) (funTypeTransp (λ X → X) (λ _ → C) p f) i) P
    ≡
    {!!}
  ) (λ q f g l →
      (λ i → subst (f ≡_) (funExt l) (funTypeTransp (λ X → X) (λ _ → C) refl f) i x)
    ≡⟨⟩
      (λ i → subst (f ≡_) (funExt l) (λ i x → transport-filler refl (f (transport-filler refl x i)) i) i x)
    ≡⟨ cong {B = λ r → f x ≡ g x} (λ r i → r i x) (substInPathsL (funExt l) (λ i x → transport-filler refl (f (transport-filler refl x i)) i)) ⟩
      (λ i → ((λ i x → transport-filler refl (f (transport-filler refl x i)) i) ∙ (funExt l)) i x)
    ≡⟨ {!!} ⟩
      {!!} ∎
  ) p P
-}
