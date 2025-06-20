module Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
    record Pullback (α : A → C) (β : B → C) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
        constructor pullback
        field
            a : A
            b : B
            eq : α a ≡ β b

    pullbackΣ : (α : A → C) (β : B → C) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
    pullbackΣ α β = Σ A λ a → Σ B λ b → α a ≡ β b

    Pullback≅pullbackΣ : (α : A → C) (β : B → C) → Iso (Pullback α β) (pullbackΣ α β)
    Iso.fun (Pullback≅pullbackΣ α β) (pullback a b eq) = a , b , eq
    Iso.inv (Pullback≅pullbackΣ α β) (a , b , eq) = pullback a b eq
    Iso.rightInv (Pullback≅pullbackΣ α β) _ = refl
    Iso.leftInv (Pullback≅pullbackΣ α β) _ = refl

    Pullback≃pullbackΣ : (α : A → C) (β : B → C) → Pullback α β ≃ pullbackΣ α β
    Pullback≃pullbackΣ α β = isoToEquiv (Pullback≅pullbackΣ α β)

    Pullback≡pullbackΣ : (α : A → C) (β : B → C) → (Pullback α β) ≡ (pullbackΣ α β)
    Pullback≡pullbackΣ α β = isoToPath (Pullback≅pullbackΣ α β)

    Pullback-proj₁ : {α : A → C} {β : B → C} → Pullback α β → A
    Pullback-proj₁ (pullback a b eq) = a

    Pullback-proj₂ : {α : A → C} {β : B → C} → Pullback α β → B
    Pullback-proj₂ (pullback a b eq) = b

    Pullback-proj₌ : {α : A → C} {β : B → C} → (x : Pullback α β) → α (Pullback-proj₁ x) ≡ β (Pullback-proj₂ x)
    Pullback-proj₌ (pullback a b eq) = eq

    pullbackΣ-proj₁ : {α : A → C} {β : B → C} → pullbackΣ α β → A
    pullbackΣ-proj₁ (a , b , eq) = a

    pullbackΣ-proj₂ : {α : A → C} {β : B → C} → pullbackΣ α β → B
    pullbackΣ-proj₂ (a , b , eq) = b

    pullbackΣ-proj₌ : {α : A → C} {β : B → C} → (x : pullbackΣ α β) → α (pullbackΣ-proj₁ x) ≡ β (pullbackΣ-proj₂ x)
    pullbackΣ-proj₌ (a , b , eq) = eq



module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
    Pullback-comm-≅ : (α : A → C) (β : B → C) → Iso (Pullback α β) (Pullback β α)
    Iso.fun (Pullback-comm-≅ α β) (pullback a b eq) = pullback b a (sym eq)
    Iso.inv (Pullback-comm-≅ α β) (pullback b a eq) = pullback a b (sym eq)
    Iso.rightInv (Pullback-comm-≅ α β) _ = refl
    Iso.leftInv (Pullback-comm-≅ α β) _ = refl

    Pullback-comm-≃ : (α : A → C) (β : B → C) → Pullback α β ≃ Pullback β α
    Pullback-comm-≃ α β = isoToEquiv (Pullback-comm-≅ α β)

    Pullback-comm-≡ : (α : A → C) (β : B → C) → Pullback α β ≡ Pullback β α
    Pullback-comm-≡ α β = isoToPath (Pullback-comm-≅ α β)


module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} where
    Pullback-fiber₂ : (f : B → A) (pick : Unit → A) → Pullback f pick ≡ fiber f (pick tt)
    Pullback-fiber₂ f pick = isoToPath (iso fun inv (λ _ → refl) (λ _ → refl)) where
        fun : Pullback f pick → fiber f (pick tt)
        fun (pullback b tt pb) = b , pb

        inv : fiber f (pick tt) → Pullback f pick
        inv (b , pb) = pullback b tt pb

    Pullback-fiber₁ : (pick : Unit → A) (f : B → A) → Pullback pick f ≡ fiber f (pick tt)
    Pullback-fiber₁ pick f = (Pullback-comm-≡ pick f) ∙ (Pullback-fiber₂ f pick)

module PastingLemma {C D E F : Type} (α : D → E) (β : E → F) (γ : C → F) where
  {-
    A --> B --> C
    |    δ| ⌟   |γ
    v     v     v
    D --> E --> F
       α     β
  -}


  B : Type
  B = pullbackΣ γ β

  η : B → C
  η = pullbackΣ-proj₁

  δ : B → E
  δ = pullbackΣ-proj₂

  fun : pullbackΣ γ (β ∘ α) → pullbackΣ δ α
  fun (c , d , p) = (c , α d , p) , d , refl

  inv : pullbackΣ δ α → pullbackΣ γ (β ∘ α)
  inv (b , d , p) = η b , d , pullbackΣ-proj₌ b ∙ cong β p

  s : section fun inv
  s ((c , e , q), d , p) = ΣPathTransport→PathΣ _ _ (lemma₁ p q , ΣPathTransport→PathΣ _ _ (lemma₂ p q , lemma₃)) where

    transport-lemma₁ : {e e' : E} (p : e ≡ e') (q : γ c ≡ β e) → subst (λ x → γ c ≡ β x) (sym p) (q ∙ cong β p) ≡ q
    transport-lemma₁ p q = J (λ _ p' → subst (λ x → γ c ≡ β x) (sym p') (q ∙ cong β p') ≡ q) (
        subst (λ x → γ c ≡ β x) refl (q ∙ refl)
      ≡⟨ JRefl (λ y _ → y) (q ∙ refl) ⟩
        q ∙ refl
      ≡⟨ sym (rUnit q) ⟩
        q ∎
      ) p

    lemma₁ : {e e' : E} (p : e ≡ e') (q : γ c ≡ β e) → (c , e' , q ∙ cong β p) ≡ (c , e , q)
    lemma₁ p q = ΣPathP (refl , ΣPathTransport→PathΣ _ _ (sym p , transport-lemma₁ p q))

    lemma₂ : {e : E} {d : D} (p : e ≡ α d) (q : γ c ≡ β e) → fst (subst (λ x → Σ D (λ b → δ x ≡ α b)) (lemma₁ p q) (d , refl)) ≡ d
    lemma₂ {e} {d} p q = J (λ _ u → fst (subst (λ x → Σ D (λ b → δ x ≡ α b)) u (d , refl)) ≡ d)
             (cong (fst {B = λ _ → α d ≡ α d}) (JRefl (λ y _ → y) (d , refl {x = α d})))
             (lemma₁ p q)

    lemma₃ : subst (λ d → e ≡ α d) (lemma₂ p q) (subst (λ y → Σ D (λ b → δ y ≡ α b)) (lemma₁ p q) (d , refl) .snd) ≡ p
    lemma₃ = J (λ e p' →
        let p = sym p' in (q : γ c ≡ β e) →
        subst (λ d → e ≡ α d) (lemma₂ p q) (subst (λ y → Σ D (λ b → δ y ≡ α b)) (lemma₁ p q) (d , refl) .snd) ≡ p
      ) (λ q →
        let r = λ i → transp (λ _ → D) i d in
          subst (λ d₁ → α d ≡ α d₁) (lemma₂ refl q) (subst (λ y → Σ D (λ b → δ y ≡ α b)) (lemma₁ refl q) (d , refl) .snd)
        ≡⟨⟩
          subst (λ d₁ → α d ≡ α d₁) (subst {y = d} (λ _ → subst {y = d} (λ _ → D) refl d ≡ d) refl r) (subst (λ d' → α d ≡ α d') (sym r) refl)
        ≡⟨ funExt⁻ (cong (subst (λ d₁ → α d ≡ α d₁)) (lemma₃' r)) (subst (λ d' → α d ≡ α d') (sym r) refl) ⟩
          subst (λ d' → α d ≡ α d') r (subst (λ d' → α d ≡ α d') (sym r) refl)
        ≡⟨ subst-sym' {B = (λ d' → α d ≡ α d')} r (refl {x = α d}) ⟩
          refl ∎
      ) (sym p) q where

      lemma₃' : (r : subst {y = d} (λ _ → D) refl d ≡ d) → subst {y = d} (λ _ → subst {y = d} (λ _ → D) refl d ≡ d) refl r ≡ r
      lemma₃' r = JRefl (λ y x → y) r

      subst-sym : {A : Type} {B : A → Type} {x y : A} (p : x ≡ y) (u : B x) → subst B (sym p) (subst B p u) ≡ u
      subst-sym {A} {B} p u = J (λ _ q → subst B (sym q) (subst B q u) ≡ u) (
                subst B refl (subst B refl u)
            ≡⟨ cong (subst B refl) (JRefl (λ a _ → a) u) ⟩
                subst B refl u
            ≡⟨ JRefl (λ a _ → a) u ⟩
                u ∎
        ) p

      subst-sym' : {A : Type} {B : A → Type} {x y : A} (p : x ≡ y) (u : B y) → subst B p (subst B (sym p) u) ≡ u
      subst-sym' {A} {B} p u = subst-sym {A} {B} (sym p) u


  r : retract fun inv
  r (c , d , p) = ΣPathP (refl , ΣPathP (refl , sym (rUnit p)))

  pasting-lemmaΣ : pullbackΣ γ (β ∘ α) ≡ pullbackΣ δ α
  pasting-lemmaΣ = isoToPath (iso fun inv s r)

  pasting-lemma : Pullback γ (β ∘ α) ≡ Pullback δ α
  pasting-lemma = Pullback≡pullbackΣ γ (β ∘ α) ∙ pasting-lemmaΣ ∙ sym (Pullback≡pullbackΣ δ α)
