open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Functions.Fibration
open import Cubical.Categories.Category

cong-fun : {A B : Type} (f g : A → B) (p : f ≡ g) (x : A) → f x ≡ g x
cong-fun f _ p x = J (λ g' _ → f x ≡ g' x) refl p

Set : Type₁
Set = Σ Type (λ A → isSet A)

fib : {A B : Type} → (A → B) → B → Type
fib {A} f y = Σ A (λ x → f x ≡ y)

isCovering₀ : {A B : Type} (f : B → A) → Type
isCovering₀ {A} f = (y : A) → isSet (fib f y)

record Covering₀ (A : Type) : Type₁ where
  field
    B : Type
    f : B → A
    p : isCovering₀ f

-- LEMMA 7.
isCovering₀IsProp : {A B : Type} (f : B → A) → isProp (isCovering₀ f)
isCovering₀IsProp f = isPropΠ (λ _ → isPropIsSet)

-- LEMMA 8. (special case for n = 0)
Covering₀A≃A→Set : {A : Type} → Covering₀ A ≃ (A → Set)
Covering₀A≃A→Set {A} =
    Covering₀ A
  ≃⟨ equiv₁ ⟩
    Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fib f x))
  ≃⟨ equiv₂ ⟩
    Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x))
  ≃⟨ equiv₃ ⟩
    (A → Set)
  ■  where

  equiv₁ : Covering₀ A ≃ Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fib f x))
  equiv₁ = isoToEquiv (iso to of (λ _ → refl) (λ _ → refl)) where

    to : Covering₀ A → Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fib f x))
    to record { B = B ; f = f ; p = p } = (B , f) , p

    of : Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fib f x)) → Covering₀ A
    of ((B , f) , p) = record { B = B ; f = f ; p = p }


  equiv₂ : Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fib f x)) ≃ Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x))
  equiv₂ = Σ-cong-equiv-fst (fibrationEquiv A ℓ-zero)

  equiv₃ : Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x)) ≃ (A → Set)
  equiv₃ = isoToEquiv (iso to of (λ _ → refl) (λ _ → refl)) where

    to : Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x)) → A → Set
    to (f⁻¹ , f⁻¹-set) x = f⁻¹ x , f⁻¹-set x

    of : (A → Set) → Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x))
    of f⁻¹ = (λ x → f⁻¹ x  .fst) , (λ x → f⁻¹ x .snd)

_→Cov₀_ : {A : Type} → Covering₀ A → Covering₀ A → Type
record { B = B ; f = f } →Cov₀ record { B = C ; f = g } = Σ (B → C) (λ h → (x : B) → g (h x) ≡ f x)

UniversalCovering₀ : (A : Type) → Type₁
UniversalCovering₀ A = Σ (Covering₀ A) (λ Cᵤ → (C : Covering₀ A) → Cᵤ →Cov₀ C)

id→Cov₀ : {A : Type} → {C : Covering₀ A} → C →Cov₀ C
id→Cov₀ = (λ z → z) , λ _ → refl

∘→Cov₀ : {A : Type} {B C D : Covering₀ A} → B →Cov₀ C → C →Cov₀ D → B →Cov₀ D
∘→Cov₀ {A} {B} {C} {D} (q₁ , p₁) (q₂ , p₂) = q₂ ∘ q₁ , (λ x →
      D .Covering₀.f (q₂ (q₁ x))
    ≡⟨ p₂ (q₁ x) ⟩
      C .Covering₀.f (q₁ x)
    ≡⟨ p₁ x ⟩
      B .Covering₀.f x ∎
  )

∘→Cov₀-snd : {A : Type} {B C D : Covering₀ A} ((u , pu) : B →Cov₀ C) ((v , pv) : C →Cov₀ D) (x : B .Covering₀.B) → (∘→Cov₀ {A} {B} {C} {D} (u , pu) (v , pv) .snd x) ≡ (pv (u x)) ∙ pu x
∘→Cov₀-snd {A} {B} {C} {D} (u , pu) (v , pv) x =
    ∘→Cov₀ {A} {B} {C} {D} (u , pu) (v , pv) .snd x
  ≡⟨⟩
    (pv (u x)) ∙ pu x ∙ refl
  ≡⟨ cong (_∙_ (pv (u x))) (sym (rUnit (pu x))) ⟩
    pv (u x) ∙ pu x ∎


∘→Cov₀-IdL : {A : Type} {B C : Covering₀ A} (f : B →Cov₀ C) → ∘→Cov₀ {A} {B} {B} {C} (id→Cov₀ {A} {B}) f ≡ f
∘→Cov₀-IdL {A} {B} {C} (h , p) = ΣPathP ((λ _ x → h x) , funExt (λ x →
      (p x) ∙ (refl ∙ refl)
    ≡⟨ cong (_∙_ (p x)) (sym (rUnit refl)) ⟩
      (p x) ∙ refl
    ≡⟨ sym (rUnit (p x)) ⟩
      p x ∎
  ))

∘→Cov₀-IdR : {A : Type} {B C : Covering₀ A} (f : B →Cov₀ C) → ∘→Cov₀ {A} {B} {C} {C} f (id→Cov₀ {A} {C}) ≡ f
∘→Cov₀-IdR {A} {B} {C} (h , p) = ΣPathP ((λ _ x → h x) , funExt (λ x → 
      refl ∙ (p x ∙ refl)
    ≡⟨ sym (lUnit (p x ∙ refl)) ⟩
      p x ∙ refl
    ≡⟨ sym (rUnit (p x)) ⟩
      p x ∎
 ))

∘→Cov₀-Assoc : {A : Type} {B C D E : Covering₀ A} (u : B →Cov₀ C) (v : C →Cov₀ D) (w : D →Cov₀ E) → ∘→Cov₀ {A} {B} {D} {E} (∘→Cov₀ {A} {B} {C} {D} u v) w ≡ ∘→Cov₀ {A} {B} {C} {E} u (∘→Cov₀ {A} {C} {D} {E} v w)
∘→Cov₀-Assoc {A} {B} {C} {D} {E} (u , pu) (v , pv) (w , pw) = ΣPathP ((λ _ x → w (v (u x))) , funExt λ x →
      (pw (∘→Cov₀ {A} {B} {C} {D} (u , pu) (v , pv) .fst x)) ∙ ((∘→Cov₀ {A} {B} {C} {D} (u , pu) (v , pv) .snd x) ∙ refl)
    ≡⟨ lemma₁ _ _ ⟩
      (pw (v (u x))) ∙ (∘→Cov₀ {A} {B} {C} {D} (u , pu) (v , pv) .snd x)
    ≡⟨ cong (_∙_ (pw (v (u x)))) (∘→Cov₀-snd {A} {B} {C} {D} (u , pu) (v , pv) x) ⟩
      (pw (v (u x))) ∙ (pv (u x)) ∙ (pu x)
    ≡⟨ assoc _ _ _ ⟩
      ((pw (v (u x))) ∙ (pv (u x))) ∙ (pu x)
    ≡⟨ sym (lemma₁ (pw (v (u x)) ∙ pv (u x)) (pu x)) ⟩
      ((pw (v (u x))) ∙ (pv (u x))) ∙ ((pu x) ∙ refl)
    ≡⟨ lemma₂ _ _ _ (sym (lemma₃ x (u , pu) (v , pv) (w , pw))) ⟩
      (∘→Cov₀ {A} {C} {D} {E} (v , pv) (w , pw) .snd (u x)) ∙ ((pu x) ∙ refl) ∎
  ) where

  lemma₁ : {A : Type} {a b c : A} (u : a ≡ b) (v : b ≡ c) → u ∙ (v ∙ refl) ≡ u ∙ v
  lemma₁ u v = cong (_∙_ u) (sym (rUnit v))

  lemma₂ : {A : Type} {a b c : A} (u u' : a ≡ b) (v : b ≡ c) → u ≡ u' → u ∙ v ≡ u' ∙ v
  lemma₂ u u' v p = J (λ u'' q → u ∙ v ≡ u'' ∙ v) refl p

  lemma₃ : (x : B .Covering₀.B) ((u , pu) : B →Cov₀ C) ((v , pv) : C →Cov₀ D) ((w , pw) : D →Cov₀ E) → (∘→Cov₀ {A} {C} {D} {E} (v , pv) (w , pw) .snd (u x)) ≡ ((pw (v (u x))) ∙ (pv (u x)))
  lemma₃ x (u , pu) (v , pv) (w , pw) = ∘→Cov₀-snd {A} {C} {D} {E} (v , pv) (w , pw) (u x)

isSet-B-Cov₀ : {A : Type} {C : Covering₀ A} → isSet (C .Covering₀.B)
isSet-B-Cov₀ = {!!} -- C'est juste faux, ça :(

isSet→Cov₀ : {A : Type} {B C : Covering₀ A} → isSet (B →Cov₀ C)
isSet→Cov₀ = isSetΣ (isSetΠ (λ x → {!!})) (λ x → {!!}) -- Pas sûr que ça soit prouvable, c'est peut-être faux

Covering₀-Category : (A : Type) → Category (ℓ-suc ℓ-zero) ℓ-zero
Covering₀-Category A = record
                        { ob = Covering₀ A
                        ; Hom[_,_] = _→Cov₀_
                        ; id = id→Cov₀
                        ; _⋆_ = ∘→Cov₀
                        ; ⋆IdL = ∘→Cov₀-IdL
                        ; ⋆IdR = ∘→Cov₀-IdL
                        ; ⋆Assoc = ∘→Cov₀-Assoc
                        ; isSetHom = isSet→Cov₀
                        }

-- UnivCoveing₀-≅ : {A : Type} (Cᵤ Cᵤ' : UniversalCovering₀ A) → Cᵤ ≅ Cᵤ'
-- UnivCoveing₀-≅ Cᵤ Cᵤ' = ?
