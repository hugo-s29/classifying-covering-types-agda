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
open import Paths

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




transport-fun :
  {A B C : Type}
  (p : A ≡ B)
  (f : A → C)
  (g : B → C)
  →
  (subst (λ X → X → C) p f ≡ g) ≅ ((a : A) → f a ≡ g (transport p a))
transport-fun {A = A} {C = C} = J (λ B p →
    (f : A → C) (g : B → C) → (subst (λ X → X → C) p f ≡ g) ≅ ((a : A) → f a ≡ g (transport p a))
  ) lemma where

  lemma : (f g : A → C) →
    (transport refl f ≡ g) ≅ ((a : A) → f a ≡ g (transport refl a))
  lemma f g ._≅_.fun tr-f≡g a = funExt⁻ (transportRefl f ⁻¹ ∙ tr-f≡g) a ∙ cong g (transportRefl a) ⁻¹
  lemma f g ._≅_.inv h = transportRefl f ∙ funExt λ a → h a ∙ cong g (transportRefl a)
  lemma f g ._≅_.rightInv h = funExt (λ a →
      funExt⁻ (transportRefl f ⁻¹ ∙ transportRefl f ∙ funExt (λ a₁ → h a₁ ∙ cong g (transportRefl a₁))) a ∙ cong g (transportRefl a) ⁻¹
    ≡⟨ cong (λ x → funExt⁻ x a ∙ cong g (transportRefl a) ⁻¹) (assoc _ _ _ ∙ cong (_∙ funExt (λ a₁ → h a₁ ∙ cong g (transportRefl a₁))) (lCancel (transportRefl f)) ∙ lUnit (funExt (λ a₁ → h a₁ ∙ cong g (transportRefl a₁))) ⁻¹) ⟩
      funExt⁻ (funExt (λ a₁ → h a₁ ∙ cong g (transportRefl a₁))) a ∙ cong g (transportRefl a) ⁻¹
    ≡⟨⟩
      (h a ∙ cong g (transportRefl a)) ∙ cong g (transportRefl a) ⁻¹
    ≡⟨ assoc _ _ _ ⁻¹ ⟩
      h a ∙ cong g (transportRefl a) ∙ cong g (transportRefl a) ⁻¹
    ≡⟨ cong (h a ∙_) (rCancel (cong g (transportRefl a))) ⟩
      h a ∙ refl
    ≡⟨ rUnit (h a) ⁻¹ ⟩
      h a ∎
    )
  lemma f g ._≅_.leftInv tr-f≡g =
      transportRefl f ∙ funExt (λ a → (funExt⁻ (transportRefl f ⁻¹ ∙ tr-f≡g) a ∙ cong g (transportRefl a) ⁻¹) ∙ cong g (transportRefl a))
    ≡⟨ cong (λ x → transportRefl f ∙ funExt (λ a → funExt⁻ x a)) (assoc _ _ _ ⁻¹) ⟩
      transportRefl f ∙ funExt (λ a → (funExt⁻ (transportRefl f ⁻¹ ∙ tr-f≡g) a ∙ (cong g (transportRefl a) ⁻¹ ∙ cong g (transportRefl a))))
    ≡⟨ cong (λ x → transportRefl f ∙ funExt (λ a → funExt⁻ ((transportRefl f ⁻¹ ∙ tr-f≡g) ∙ x) a)) (lCancel _) ⟩
      transportRefl f ∙ funExt (λ a → (funExt⁻ (transportRefl f ⁻¹ ∙ tr-f≡g) a ∙ refl))
    ≡⟨ cong (λ x → transportRefl f ∙ funExt (λ a → funExt⁻ x a)) (rUnit _ ⁻¹) ⟩
      transportRefl f ∙ funExt (λ a → funExt⁻ (transportRefl f ⁻¹ ∙ tr-f≡g) a)
    ≡⟨⟩
      transportRefl f ∙ transportRefl f ⁻¹ ∙ tr-f≡g
    ≡⟨ assoc _ _ _ ∙ cong (_∙ tr-f≡g) (rCancel (transportRefl f)) ∙ lUnit _ ⁻¹ ⟩
      tr-f≡g ∎



-}

cong-concat :
  {A : Type}
  {B : Type}
  (f : (a : A) → B)
  {x y z : A}
  (p : x ≡ y) (q : y ≡ z)
  →
  cong f (p ∙ q) ≡ cong f p ∙ cong f q
cong-concat f p = J (λ _ q → cong f (p ∙ q) ≡ cong f p ∙ cong f q ) (cong (cong f) (rUnit p ⁻¹) ∙ rUnit (cong f p))


magic :
  {A : Type}
  (x : A)
  →
  congP (λ i x → transportRefl x i) (transportRefl x) ≡ transportRefl _ ∙ transportRefl _
magic x = {!!}

test :
  {A B C : Type}
  (f : A → C)
  (k : A ≅ B)
  (a : A)
  →
  congP (λ i b → (transportRefl (f (transport⁻ (isoToPath k) b)) ∙ cong f (transportIsoToPath⁻ k b)) i) (transportIsoToPath k a)
  ≡
  transportRefl (f (transport⁻ (isoToPath k) (transport (isoToPath k) a)))
  ∙ cong f (transport⁻Transport (isoToPath k) a ∙ _≅_.leftInv k a ⁻¹)
test f k a =
    congP (λ i b → (transportRefl (f (transport⁻ (isoToPath k) b)) ∙ cong f (transportIsoToPath⁻ k b)) i) (transportIsoToPath k a)
  ≡⟨⟩
    congP (λ i b → (transportRefl (f (_≅_.inv k (transport refl b))) ∙ cong f (cong (_≅_.inv k) (transportRefl b))) i) (transportRefl (_≅_.fun k a))
  ≡⟨ {!!} ⟩ -- congP (p ∙ q) (r ∙ s) ≡ congP p r ∙ congP q s
    congP (λ i b → (transportRefl (f (_≅_.inv k (transport refl b)))) i) refl ∙ congP (λ i b → cong f (cong (_≅_.inv k) (transportRefl b)) i) (transportRefl (_≅_.fun k a))
  ≡⟨ cong (λ u → u ∙ congP (λ i b → cong f (cong (_≅_.inv k) (transportRefl b)) i) (transportRefl (_≅_.fun k a))) (lemma (λ b → f (_≅_.inv k (transport refl b))) (transport refl (_≅_.fun k a)) (transport refl (_≅_.fun k a)) refl ∙ rUnit _ ⁻¹) ⟩
    transportRefl (f (_≅_.inv k (transport refl (transport refl (_≅_.fun k a))))) ∙ congP (λ i b → f ((_≅_.inv k) (transportRefl b i))) (transportRefl (_≅_.fun k a))
  ≡⟨⟩
    transportRefl (f (transport⁻ (isoToPath k) (transport (isoToPath k) a))) ∙ congP (λ i b → f ((_≅_.inv k) (transportRefl b i))) (transportRefl (_≅_.fun k a))
  ≡⟨⟩
    transportRefl (f (transport⁻ (isoToPath k) (transport (isoToPath k) a))) ∙ cong (f ∘ _≅_.inv k) (congP (λ i x → transportRefl x i) (transportRefl (_≅_.fun k a)))
  ≡⟨ {!!} ⟩
    transportRefl (f (transport⁻ (isoToPath k) (transport (isoToPath k) a))) ∙ cong (f ∘ _≅_.inv k) (transportRefl (transport refl (_≅_.fun k a)) ∙ transportRefl (_≅_.fun k a))
  ≡⟨ {!!} ⟩
    transportRefl (f (transport⁻ (isoToPath k) (transport (isoToPath k) a))) ∙ cong f (λ i → (transport⁻Transport (isoToPath k) a ∙ {!!}) i)
  ≡⟨ {!!} ⟩
    transportRefl (f (transport⁻ (isoToPath k) (transport (isoToPath k) a))) ∙ cong f (transport⁻Transport (isoToPath k) a ∙ _≅_.leftInv k a ⁻¹) ∎
  where


  lem : cong (_≅_.inv k) (transportRefl (transport refl (_≅_.fun k a)) ∙ transportRefl (_≅_.fun k a)) ≡ transport⁻Transport (isoToPath k) a ∙ _≅_.leftInv k a ⁻¹
  lem =
      cong (_≅_.inv k) (transportRefl (transport (isoToPath k) a) ∙ transportRefl (_≅_.fun k a))
    ≡⟨ {!!} ⟩
      {!!}
    ≡⟨ {!!} ⟩
      transport⁻Transport (isoToPath k) a ∙ _≅_.leftInv k a ⁻¹ ∎
