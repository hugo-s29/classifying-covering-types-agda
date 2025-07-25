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


sym-conc :
  {A : Type}
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  →
  (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
sym-conc p = J (λ _ q → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹) (
    (p ∙ refl) ⁻¹
  ≡⟨ cong _⁻¹ (rUnit p ⁻¹) ⟩
    p ⁻¹
  ≡⟨ lUnit (p ⁻¹) ⟩
    refl ∙ p ⁻¹ ∎
  )

congPTransportRefl :
  {A B : Type}
  (f : A → B) (x y : A) (p : x ≡ y) →
  congP (λ i u → transportRefl (f u) i) p ≡ transportRefl (f x) ∙ cong f p
congPTransportRefl f x _ = J (λ _ p →
    congP (λ i u → transportRefl (f u) i) p
    ≡ transportRefl (f x) ∙ cong f p
  ) (rUnit (transportRefl (f x)))

congP-funTypeTransp :
  {A B C : Type}
  (f : A → C)
  (x : A)
  (p : A ≡ B)
  →
  congP (λ i a → funTypeTransp (λ X → X) (λ _ → C) p f i a) (transport-filler p x)
  ≡ cong f (transport⁻Transport p x) ⁻¹ ∙ transportRefl (f (transport⁻ p (transport p x))) ⁻¹
congP-funTypeTransp {A = A} {C = C} f x = J (λ _ p →
  congP (λ i a → funTypeTransp (λ X → X) (λ _ → C) p f i a) (transport-filler p x)
  ≡ cong f (transport⁻Transport p x) ⁻¹ ∙ transportRefl (f (transport⁻ p (transport p x))) ⁻¹)
  (
      congP (λ i a → funTypeTransp (λ X → X) (λ _ → C) refl f i a) (transport-filler refl x)
    ≡⟨⟩
      congP (λ i a → transportRefl (f (transportRefl a i)) i) (transportRefl x) ⁻¹
    ≡⟨⟩
      (λ i → transportRefl (f (transportRefl (transportRefl x i) i)) i) ⁻¹
    ≡⟨ cong _⁻¹ (congPTransportRefl f (transport⁻ refl (transport refl x)) x (λ i → transportRefl (transportRefl x i) i)) ⟩
      (transportRefl (f (transport⁻ refl (transport refl x))) ∙ (λ i → f (transportRefl (transportRefl x i) i))) ⁻¹
    ≡⟨ sym-conc _ _ ⟩
      (λ i → f (transportRefl (transportRefl x i) i)) ⁻¹ ∙ transportRefl (f (transport⁻ refl (transport refl x))) ⁻¹
    ≡⟨⟩
      cong f (transport⁻Transport refl x) ⁻¹ ∙ transportRefl (f (transport⁻ refl (transport refl x))) ⁻¹ ∎
  )

private
  {- This was taken from the Cubical Library (Foundations/Isomorphism.agda) -}
  module Iso→Equiv (A B : Type) (f : A → B) (g : B → A) (s : section f g) (t : retract f g) (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
    fill0 : I → I → A
    fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                              ; (i = i0) → g y })
                    (inS (g (p0 (~ i))))

    fill1 : I → I → A
    fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                              ; (i = i0) → g y })
                    (inS (g (p1 (~ i))))

    fill2 : I → I → A
    fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                              ; (i = i0) → fill0 k i1 })
                    (inS (g y))

    p : x0 ≡ x1
    p i = fill2 i i1

module _ {A B : Type} (f : A → B) (g : B → A) (rinv : section f g) (linv : retract f g) (h : (b : B) → cong g (rinv b) ≡ linv (g b)) (a : A) where
  private
    biinv : BiInvEquiv A B
    biinv .BiInvEquiv.fun = f
    biinv .BiInvEquiv.invr = g
    biinv .BiInvEquiv.invr-rightInv = rinv
    biinv .BiInvEquiv.invl = g
    biinv .BiInvEquiv.invl-leftInv = linv

    A≃B : A ≃ B
    A≃B = biInvEquiv→Equiv-left biinv

    rinv' : (b : B) → f (g b) ≡ b
    rinv' = BiInvEquiv.invl-rightInv biinv

    open Iso→Equiv A B f g rinv' linv (f a) (g (f a)) a (rinv' (f a)) refl

    top-fill1 : (λ i → fill1 i i1) ≡ linv a
    top-fill1 = lUnit (linv a) ⁻¹

    rinv'≡rinv : rinv' ≡ rinv
    rinv'≡rinv = funExt(λ b →
        cong f (linv (g b) ⁻¹ ∙ cong g (rinv b) ∙ refl) ⁻¹ ∙ rinv b
      ≡⟨ cong (λ u → cong f (linv (g b) ⁻¹ ∙ u) ⁻¹ ∙ rinv b) (rUnit _ ⁻¹) ⟩
        cong f (linv (g b) ⁻¹ ∙ cong g (rinv b)) ⁻¹ ∙ rinv b
      ≡⟨ cong (λ u → cong f (linv (g b) ⁻¹ ∙ u) ⁻¹ ∙ rinv b) (h b) ⟩
        cong f (linv (g b) ⁻¹ ∙ linv (g b)) ⁻¹ ∙ rinv b
      ≡⟨ cong (λ u → cong f u ⁻¹ ∙ rinv b) (lCancel (linv (g b))) ⟩
        cong f refl ⁻¹ ∙ rinv b
      ≡⟨ lUnit _ ⁻¹ ⟩
        rinv b ∎)

    h' : (b : B) → cong g (rinv' b) ≡ linv (g b)
    h' b = subst⁻ (λ u → cong g (u b) ≡ linv (g b)) rinv'≡rinv (h b)

    top-fill0 : (λ i → fill0 i i1) ≡ refl
    top-fill0 =
      cong g (rinv' (f a)) ⁻¹ ∙ linv (g (f a))
      ≡⟨ cong (cong g (rinv' (f a)) ⁻¹ ∙_) (h' (f a)) ⁻¹ ⟩
      cong g (rinv' (f a)) ⁻¹ ∙ cong g (rinv' (f a))
      ≡⟨ lCancel _ ⟩
      refl ∎

    p≡linv : p ≡ linv a
    p≡linv =
        ((λ i → fill0 i i1) ⁻¹ ∙∙ refl ∙∙ (λ i → fill1 i i1))
      ≡⟨ cong₂ (λ u v → _∙∙_∙∙_ {w = a} (u ⁻¹) refl v) top-fill0 top-fill1 ⟩
        (refl ∙∙ refl ∙∙ linv a)
      ≡⟨ lUnit _ ⁻¹ ⟩
        linv a ∎

  retEq≡linv : retEq A≃B a ≡ linv a
  retEq≡linv = p≡linv

postulate
  -- this seems reasonable
  tr⁻Tr-uaId : {A : Type} (a : A) → transport⁻Transport (ua (idEquiv A)) a ≡ transport⁻Transport refl a

ua-tr⁻Tr : {A B : Type} (A≃B : A ≃ B) (a : A) → congP (λ i b → ~uaβ A≃B b i) (uaβ A≃B a) ≡ transport⁻Transport (ua A≃B) a ∙ retEq A≃B a ⁻¹
ua-tr⁻Tr {B = B} = EquivJ (λ A A≃B → (a : A) → congP (λ i b → ~uaβ A≃B b i) (uaβ A≃B a) ≡ transport⁻Transport (ua A≃B) a ∙ retEq A≃B a ⁻¹) (λ b →
      congP (λ i x → transportRefl x i) (transportRefl b)
    ≡⟨⟩
      transport⁻Transport refl b
    ≡⟨ tr⁻Tr-uaId b ⁻¹ ⟩
      transport⁻Transport (ua (idEquiv B)) b
    ≡⟨ rUnit _ ⟩
      transport⁻Transport (ua (idEquiv B)) b ∙ refl ∎
  )


congP∙ :
  {A B : Type}
  {f g h : A → B}
  {x y z : A}
  (p : f ≡ g)
  (q : g ≡ h)
  (r : x ≡ y)
  (s : y ≡ z)
  →
  congP (λ i → (p ∙ q) i) (r ∙ s)
  ≡ congP (λ i → p i) r ∙ congP (λ i → q i) s
congP∙ {x = x} {y = y} p q r = J2 (λ _ q _ s →
  congP (λ i → (p ∙ q) i) (r ∙ s) ≡ congP (λ i → p i) r ∙ congP (λ i → q i) s) (
    congP (λ i → (p ∙ refl) i) (r ∙ refl)
  ≡⟨ cong₂ (λ u v → congP (λ i → u i) {x = x} {y = y} v) (rUnit p) (rUnit r) ⁻¹ ⟩
    congP (λ i → p i) r
  ≡⟨ rUnit _ ⟩
    congP (λ i → p i) r ∙ refl ∎
  ) q

cong∙ :
  {A B : Type}
  (f : A → B)
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  →
  cong f (p ∙ q)
  ≡ cong f p ∙ cong f q
cong∙ f p = J (λ _ q → cong f (p ∙ q) ≡ cong f p ∙ cong f q) (
    cong f (p ∙ refl)
  ≡⟨ cong (cong f) (rUnit p) ⁻¹ ⟩
    cong f p
  ≡⟨ rUnit (cong f p) ⟩
    cong f p ∙ refl ∎)

congP-subst-rUnit :
  {A B C : Type}
  {f : A → C}
  {g : B → C}
  {a : A}
  {b : B}
  (p : A ≡ B)
  (P : PathP (λ i → (p ∙ refl) i → C) f g)
  (Q : PathP (λ i → (p ∙ refl) i) a b)
  →
  congP (λ i → subst⁻ (λ u → PathP (λ i → u i → C) f g) (rUnit p) P i) (subst⁻ (λ u → PathP (λ i → u i) a b) (rUnit p) Q) ≡ congP (λ i → P i) Q
congP-subst-rUnit {A = A} {B = B} {C = C} {f = f} {g = g} {a = a} {b = b} p P Q = J (λ p rup →
          (P : PathP (λ i → p i → C) f g)
          (Q : PathP (λ i → p i) a b)
          →
          congP (λ i → subst⁻ {A = A ≡ B} (λ u → PathP (λ i → u i → C) f g) rup P i) (subst⁻ {A = A ≡ B} (λ u → PathP (λ i → u i) a b) rup Q) ≡ congP (λ i → P i) Q
      ) (λ P Q →
          (λ i → subst⁻ {A = A ≡ B} (λ u → PathP (λ i₁ → u i₁ → C) f g) refl P i (subst⁻ {A = A ≡ B} (λ u → PathP (λ i₁ → u i₁) a b) refl Q i))
      ≡⟨ cong {B = λ _ → f a ≡ g b} (λ u i → subst⁻ {A = A ≡ B} (λ u → PathP (λ i₁ → u i₁ → C) f g) refl P i (u i)) (transportRefl Q) ⟩
          (λ i → subst⁻ {A = A ≡ B} (λ u → PathP (λ i₁ → u i₁ → C) f g) (refl {x = p}) P i (Q i))
      ≡⟨ cong {B = λ _ → f a ≡ g b} (λ u i → u i (Q i)) (transportRefl P) ⟩
          congP (λ i → P i) Q ∎
      ) (rUnit p) P Q
