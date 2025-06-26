module Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

private
  transport-fun : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'} (p : A ≡ B) (f : A → C) (g : B → C) → (∀ x → f x ≡ g (transport p x)) → transport (λ i → p i → C) f ≡ g
  transport-fun {B = B} {C = C} p f =
    J (λ B p → (g : B → C) → (∀ x → f x ≡ g (transport p x)) → subst (λ X → X → C) p f ≡ g )
    (λ g h → transportRefl f ∙ funExt (λ x → (h x) ∙ (cong g (transportRefl x)))) p

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

    Pullback-transport→Σ : {α : A → C} {β : B → C} (a : A) (b : B) (p : α a ≡ β b) → pullback a b p ≡ transport (sym (Pullback≡pullbackΣ α β)) (a , b , p)
    Pullback-transport→Σ a b p = transportIsoToPath⁻ (Pullback≅pullbackΣ _ _) (a , b , p) ⁻¹

    Pullback-transport←Σ : {α : A → C} {β : B → C} (a : A) (b : B) (p : α a ≡ β b) → (a , b , p) ≡ transport (Pullback≡pullbackΣ α β) (pullback a b p)
    Pullback-transport←Σ a b p = transportIsoToPath (Pullback≅pullbackΣ _ _) (pullback a b p) ⁻¹

    Pullback-transport→Σ-proj₁ : {α : A → C} {β : B → C} (x : pullbackΣ α β) → pullbackΣ-proj₁ x ≡ Pullback-proj₁ (transport (sym (Pullback≡pullbackΣ α β)) x)
    Pullback-transport→Σ-proj₁ {α} {β} (a , b , p) = cong Pullback-proj₁ (Pullback-transport→Σ {α} {β} a b p)

    Pullback-transport→Σ-proj₂ : {α : A → C} {β : B → C} (x : pullbackΣ α β) → pullbackΣ-proj₂ x ≡ Pullback-proj₂ (transport (sym (Pullback≡pullbackΣ α β)) x)
    Pullback-transport→Σ-proj₂ {α} {β} (a , b , p) = cong Pullback-proj₂ (Pullback-transport→Σ {α} {β} a b p)

    Pullback-transport→Σ-proj₁-fun : {α : A → C} {β : B → C} → subst (λ X → X → A) (Pullback≡pullbackΣ α β ⁻¹) pullbackΣ-proj₁ ≡ Pullback-proj₁
    Pullback-transport→Σ-proj₁-fun {α} {β} = transport-fun (Pullback≡pullbackΣ α β ⁻¹) _ _ Pullback-transport→Σ-proj₁

    Pullback-transport→Σ-proj₂-fun : {α : A → C} {β : B → C} → subst (λ X → X → B) (Pullback≡pullbackΣ α β ⁻¹) pullbackΣ-proj₂ ≡ Pullback-proj₂
    Pullback-transport→Σ-proj₂-fun {α} {β} = transport-fun (Pullback≡pullbackΣ α β ⁻¹) _ _ Pullback-transport→Σ-proj₂

    Pullback-transport←Σ-proj₁ : {α : A → C} {β : B → C} (x : Pullback α β) → Pullback-proj₁ x ≡ pullbackΣ-proj₁ (transport (Pullback≡pullbackΣ α β) x)
    Pullback-transport←Σ-proj₁ {α} {β} (pullback a b eq) = cong pullbackΣ-proj₁ (Pullback-transport←Σ {α} {β} a b eq)

    Pullback-transport←Σ-proj₂ : {α : A → C} {β : B → C} (x : Pullback α β) → Pullback-proj₂ x ≡ pullbackΣ-proj₂ (transport (Pullback≡pullbackΣ α β) x)
    Pullback-transport←Σ-proj₂ {α} {β} (pullback a b eq) = cong pullbackΣ-proj₂ (Pullback-transport←Σ {α} {β} a b eq)

    Pullback-transport←Σ-proj₁-fun : {α : A → C} {β : B → C} → subst (λ X → X → A) (Pullback≡pullbackΣ α β) Pullback-proj₁ ≡ pullbackΣ-proj₁
    Pullback-transport←Σ-proj₁-fun {α} {β} = transport-fun (Pullback≡pullbackΣ α β) _ _ Pullback-transport←Σ-proj₁

    Pullback-transport←Σ-proj₂-fun : {α : A → C} {β : B → C} → subst (λ X → X → B) (Pullback≡pullbackΣ α β) Pullback-proj₂ ≡ pullbackΣ-proj₂
    Pullback-transport←Σ-proj₂-fun {α} {β} = transport-fun (Pullback≡pullbackΣ α β) _ _ Pullback-transport←Σ-proj₂

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

    Pullback-comm-≡-transport : (α : A → C) (β : B → C) (a : A) (b : B) (eq : α a ≡ β b) → (pullback b a (sym eq)) ≡ transport (Pullback-comm-≡ α β) (pullback a b eq)
    Pullback-comm-≡-transport α β a b eq = transportIsoToPath (Pullback-comm-≅ α β) (pullback a b eq) ⁻¹

    Pullback-comm-≡-proj1→2 : (α : A → C) (β : B → C) (x : Pullback α β) → Pullback-proj₁ x ≡ Pullback-proj₂ (transport (Pullback-comm-≡ α β) x)
    Pullback-comm-≡-proj1→2 α β (pullback a b eq) = cong Pullback-proj₂ (Pullback-comm-≡-transport α β a b eq)

    Pullback-comm-≡-proj2→1 : (α : A → C) (β : B → C) (x : Pullback α β) → Pullback-proj₂ x ≡ Pullback-proj₁ (transport (Pullback-comm-≡ α β) x)
    Pullback-comm-≡-proj2→1 α β (pullback a b eq) = cong Pullback-proj₁ (Pullback-comm-≡-transport α β a b eq)

    Pullback-comm-≡-proj1→2-fun : {α : A → C} {β : B → C} → subst (λ X → X → A) (Pullback-comm-≡ α β) Pullback-proj₁ ≡ Pullback-proj₂
    Pullback-comm-≡-proj1→2-fun {α} {β} = transport-fun (Pullback-comm-≡ α β) Pullback-proj₁ Pullback-proj₂ (Pullback-comm-≡-proj1→2 α β)

    Pullback-comm-≡-proj2→1-fun : {α : A → C} {β : B → C} → subst (λ X → X → B) (Pullback-comm-≡ α β) Pullback-proj₂ ≡ Pullback-proj₁
    Pullback-comm-≡-proj2→1-fun {α} {β} = transport-fun (Pullback-comm-≡ α β) Pullback-proj₂ Pullback-proj₁ (Pullback-comm-≡-proj2→1 α β)

module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where
  Pullback-transport₁ : {A' : Type ℓ} (p : A ≡ A') (α : A' → C) (β : B → C) → Pullback (α ∘ transport p) β ≡ Pullback α β
  Pullback-transport₁ p _ _ = Pullback≡pullbackΣ _ _ ∙ Σ-cong-fst p ∙ Pullback≡pullbackΣ _ _ ⁻¹

  Pullback-transport₂ : {B' : Type ℓ'} (p : B ≡ B') (α : A → C) (β : B' → C) → Pullback α (β ∘ transport p) ≡ Pullback α β
  Pullback-transport₂ p _ _ = Pullback≡pullbackΣ _ _ ∙ Σ-cong-snd (λ x → Σ-cong-fst p) ∙ Pullback≡pullbackΣ _ _ ⁻¹

  Pullback-transportα : (α α' : A → C) (β : B → C) (p : α ≡ α') → Pullback α β ≡ Pullback α' β
  Pullback-transportα _ _ β p = Pullback≡pullbackΣ _ _ ∙ Σ-cong-snd (λ a → Σ-cong-snd (λ b → cong (λ α → α a ≡ β b) p)) ∙ Pullback≡pullbackΣ _ _ ⁻¹

  Pullback-transportβ : (α : A → C) (β β' : B → C) (p : β ≡ β') → Pullback α β ≡ Pullback α β'
  Pullback-transportβ α _ _ p = Pullback≡pullbackΣ _ _ ∙ Σ-cong-snd (λ a → Σ-cong-snd (λ b → cong (λ β → α a ≡ β b) p)) ∙ Pullback≡pullbackΣ _ _ ⁻¹

module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} where
    Pullback-fiber₂ : (f : B → A) (pick : Unit → A) → Pullback f pick ≡ fiber f (pick tt)
    Pullback-fiber₂ f pick = isoToPath (iso fun inv (λ _ → refl) (λ _ → refl)) where
        fun : Pullback f pick → fiber f (pick tt)
        fun (pullback b tt pb) = b , pb

        inv : fiber f (pick tt) → Pullback f pick
        inv (b , pb) = pullback b tt pb

    Pullback-fiber₁ : (pick : Unit → A) (f : B → A) → Pullback pick f ≡ fiber f (pick tt)
    Pullback-fiber₁ pick f = (Pullback-comm-≡ pick f) ∙ (Pullback-fiber₂ f pick)

module PastingLemma-horizontal {ℓ : Level} {C D E F : Type ℓ} (α : D → E) (β : E → F) (γ : C → F) where
  {- Horizontal pasting lemma
    A --> B --> C
    | ⌟  δ| ⌟   |γ
    v     v     v
    D --> E --> F
       α     β
  -}


  B : Type _
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

      subst-sym : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (p : x ≡ y) (u : B x) → subst B (sym p) (subst B p u) ≡ u
      subst-sym {A = A} {B = B} p u = J (λ _ q → subst B (sym q) (subst B q u) ≡ u) (
                subst B refl (subst B refl u)
            ≡⟨ cong (subst B refl) (JRefl (λ a _ → a) u) ⟩
                subst B refl u
            ≡⟨ JRefl (λ a _ → a) u ⟩
                u ∎
        ) p

      subst-sym' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (p : x ≡ y) (u : B y) → subst B p (subst B (sym p) u) ≡ u
      subst-sym' {A = A} {B = B} p u = subst-sym {A = A} {B = B} (sym p) u


  r : retract fun inv
  r (c , d , p) = ΣPathP (refl , ΣPathP (refl , sym (rUnit p)))

  pasting-lemmaΣ : pullbackΣ γ (β ∘ α) ≡ pullbackΣ δ α
  pasting-lemmaΣ = isoToPath (iso fun inv s r)

  pasting-lemma : Pullback γ (β ∘ α) ≡ Pullback δ α
  pasting-lemma = Pullback≡pullbackΣ _ _ ∙ pasting-lemmaΣ ∙ Pullback≡pullbackΣ _ _ ⁻¹


module PastingLemma-vertical {ℓ : Level} {B D E F : Type ℓ} (α : B → D) (β : D → F) (γ : E → F) where
  {-
    A ---> B
    | ⌟    |
    |      | α
    v  δ   v
    C ---> D
    | ⌟    |
    |      | β
    v      v
    E ---> F
       γ
  -}


  C : Type _
  C = pullbackΣ β γ

  η : C → E
  η = pullbackΣ-proj₂

  δ : C → D
  δ = pullbackΣ-proj₁

  C' : Type _
  C' = pullbackΣ γ β

  {- We go back to the horizontal pasting lemma :

    A' --> C' --> E
    |    δ'| ⌟    |γ
    v      v      v
    B  --> D  --> F
       α       β

    we use the commutativity of the pullback
  -}

  private
    C'≡C : C' ≡ C
    C'≡C = Pullback≡pullbackΣ _ _ ⁻¹ ∙ Pullback-comm-≡ _ _ ∙ Pullback≡pullbackΣ _ _

    lemma₀ : (e : E) (d : D) (p : γ e ≡ β d) → transport C'≡C (e , d , p) ≡ (d , e , p ⁻¹)
    lemma₀ e d p =
        transport (Pullback≡pullbackΣ γ β ⁻¹ ∙ (Pullback-comm-≡ γ β ∙ Pullback≡pullbackΣ β γ)) (e , d , p)
      ≡⟨ transportComposite (Pullback≡pullbackΣ γ β ⁻¹) (Pullback-comm-≡ γ β ∙ Pullback≡pullbackΣ β γ) (e , d , p) ⟩
        transport (Pullback-comm-≡ γ β ∙ Pullback≡pullbackΣ β γ) (transport (Pullback≡pullbackΣ γ β ⁻¹) (e , d , p))
      ≡⟨ transportComposite (Pullback-comm-≡ γ β) (Pullback≡pullbackΣ β γ) (transport (Pullback≡pullbackΣ γ β ⁻¹) (e , d , p)) ⟩
        transport (Pullback≡pullbackΣ β γ) (transport (Pullback-comm-≡ γ β) (transport (Pullback≡pullbackΣ γ β ⁻¹) (e , d , p)))
      ≡⟨ cong (transport (Pullback≡pullbackΣ β γ)) (cong (transport (Pullback-comm-≡ γ β)) (Pullback-transport→Σ e d p ⁻¹)) ⟩
        transport (Pullback≡pullbackΣ β γ) (transport (Pullback-comm-≡ γ β) (pullback e d p))
      ≡⟨ cong (transport (Pullback≡pullbackΣ β γ)) (Pullback-comm-≡-transport γ β e d p ⁻¹) ⟩
        transport (Pullback≡pullbackΣ β γ) (pullback d e (p ⁻¹))
      ≡⟨ Pullback-transport←Σ d e (p ⁻¹) ⁻¹ ⟩
        d , e , p ⁻¹ ∎

    lemma : (x : C') → pullbackΣ-proj₂ x ≡ δ (transport C'≡C x)
    lemma (e , d , p) = cong δ (lemma₀ e d p ⁻¹)

  pasting-lemma : Pullback (β ∘ α) γ ≡ Pullback α δ
  pasting-lemma =
      Pullback (β ∘ α) γ
    ≡⟨ Pullback-comm-≡ _ _ ⟩
      Pullback γ (β ∘ α)
    ≡⟨ PastingLemma-horizontal.pasting-lemma α β γ ⟩
      Pullback pullbackΣ-proj₂ α
    ≡⟨ Pullback-comm-≡ _ _ ⟩
      Pullback {B = C'} α pullbackΣ-proj₂
    ≡⟨ Pullback-transportβ α pullbackΣ-proj₂ (δ ∘ transport C'≡C) (funExt lemma) ⟩
      Pullback {B = C'} α (δ ∘ transport C'≡C)
    ≡⟨ Pullback-transport₂ C'≡C α δ ⟩
      Pullback α δ ∎
