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

pick : {W : Type} (a : W) → ⊤ → W
pick x tt = x

Set : Type₁
Set = Σ Type (λ A → isSet A)

isCovering₀ : {A B : Type} (f : B → A) → Type
isCovering₀ {A} f = (y : A) → isSet (fiber f y)

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
    Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fiber f x))
  ≃⟨ equiv₂ ⟩
    Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x))
  ≃⟨ equiv₃ ⟩
    (A → Set)
  ■  where

  equiv₁ : Covering₀ A ≃ Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fiber f x))
  equiv₁ = isoToEquiv (iso to of (λ _ → refl) (λ _ → refl)) where

    to : Covering₀ A → Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fiber f x))
    to record { B = B ; f = f ; p = p } = (B , f) , p

    of : Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fiber f x)) → Covering₀ A
    of ((B , f) , p) = record { B = B ; f = f ; p = p }


  equiv₂ : Σ (Σ Type (λ B → B → A)) (λ (_ , f) → (x : A) → isSet (fiber f x)) ≃ Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x))
  equiv₂ = Σ-cong-equiv-fst (fibrationEquiv A ℓ-zero)

  equiv₃ : Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x)) ≃ (A → Set)
  equiv₃ = isoToEquiv (iso to of (λ _ → refl) (λ _ → refl)) where

    to : Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x)) → A → Set
    to (f⁻¹ , f⁻¹-set) x = f⁻¹ x , f⁻¹-set x

    of : (A → Set) → Σ (A → Type) (λ f⁻¹ → (x : A) → isSet (f⁻¹ x))
    of f⁻¹ = (λ x → f⁻¹ x  .fst) , (λ x → f⁻¹ x .snd)

_→Cov₀_ : {A : Type} → Covering₀ A → Covering₀ A → Type
record { B = B ; f = f } →Cov₀ record { B = C ; f = g } = Σ (B → C) (λ h → (x : B) → g (h x) ≡ f x)

idCov₀ : {A : Type} → {C : Covering₀ A} → C →Cov₀ C
idCov₀ = (λ z → z) , λ _ → refl

∘→Cov₀ : {A : Type} {B C D : Covering₀ A} → B →Cov₀ C → C →Cov₀ D → B →Cov₀ D
∘→Cov₀ {A} {B} {C} {D} (q₁ , p₁) (q₂ , p₂) = q₂ ∘ q₁ , (λ x →
      D .Covering₀.f (q₂ (q₁ x))
    ≡⟨ p₂ (q₁ x) ⟩
      C .Covering₀.f (q₁ x)
    ≡⟨ p₁ x ⟩
      B .Covering₀.f x ∎
  )

_∘Cov₀_ : {A : Type} {B C D : Covering₀ A} → C →Cov₀ D → B →Cov₀ C → B →Cov₀ D
_∘Cov₀_ {A} {B} {C} {D} f g = ∘→Cov₀ {A} {B} {C} {D} g f

∘→Cov₀-snd : {A : Type} {B C D : Covering₀ A} ((u , pu) : B →Cov₀ C) ((v , pv) : C →Cov₀ D) (x : B .Covering₀.B) → (∘→Cov₀ {A} {B} {C} {D} (u , pu) (v , pv) .snd x) ≡ (pv (u x)) ∙ pu x
∘→Cov₀-snd {A} {B} {C} {D} (u , pu) (v , pv) x =
    ∘→Cov₀ {A} {B} {C} {D} (u , pu) (v , pv) .snd x
  ≡⟨⟩
    (pv (u x)) ∙ pu x ∙ refl
  ≡⟨ cong (_∙_ (pv (u x))) (sym (rUnit (pu x))) ⟩
    pv (u x) ∙ pu x ∎


∘→Cov₀-IdL : {A : Type} {B C : Covering₀ A} (f : B →Cov₀ C) → ∘→Cov₀ {A} {B} {B} {C} (idCov₀ {A} {B}) f ≡ f
∘→Cov₀-IdL {A} {B} {C} (h , p) = ΣPathP ((λ _ x → h x) , funExt (λ x →
      (p x) ∙ (refl ∙ refl)
    ≡⟨ cong (_∙_ (p x)) (sym (rUnit refl)) ⟩
      (p x) ∙ refl
    ≡⟨ sym (rUnit (p x)) ⟩
      p x ∎
  ))

∘→Cov₀-IdR : {A : Type} {B C : Covering₀ A} (f : B →Cov₀ C) → ∘→Cov₀ {A} {B} {C} {C} f (idCov₀ {A} {C}) ≡ f
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

{-
Cov₀Cat : (A : Type) → WildCat (ℓ-suc ℓ-zero) ℓ-zero
Cov₀Cat A = record
           { ob = Covering₀ A
           ; Hom[_,_] = _→Cov₀_
           ; id = idCov₀
           ; _⋆_ = ∘→Cov₀
           ; ⋆IdL = ∘→Cov₀-IdL
           ; ⋆IdR = ∘→Cov₀-IdL
           ; ⋆Assoc = ∘→Cov₀-Assoc
           }
-}

isConnected' : (A : Type) → Type
isConnected' A = ∥ A ∥₁ × ((x y : A) → ∥ x ≡ y ∥₁)

isConnected'IsProp : {A : Type} → isProp (isConnected' A)
isConnected'IsProp {A} = isProp× isPropPropTrunc (isPropΠ λ _ → isPropΠ λ _ → isPropPropTrunc)

isConnected'Σ : {A : Type} {B : A → Type} → isConnected' A → (∀ x → isConnected' (B x)) → isConnected' (Σ A B)
isConnected'Σ {A} {B} (⋆A , hA) hB = basept , path where

  basept' : ∥ ∥ Σ A B ∥₁ ∥₁
  basept' = ∥-∥-map (λ ⋆A → ∥-∥-map (λ ⋆B → (⋆A , ⋆B)) (hB ⋆A .fst)) ⋆A

  basept : ∥ Σ A B ∥₁
  basept = transport (propTruncIdempotent isPropPropTrunc) basept'

  path' : (a a' : A) (b : B a) (b' : B a') → ∥ ∥ (a , b) ≡ (a' , b') ∥₁ ∥₁
  path' a a' b b' = ∥-∥-map (λ p → ∥-∥-map (λ q →  ΣPathTransport→PathΣ (a , b) (a' , b') (p , q)) (hB a' .snd (subst B p b) b')) (hA a a')

  path : (x y : Σ A B) → ∥ x ≡ y ∥₁
  path (a , b) (a' , b') = transport (propTruncIdempotent isPropPropTrunc) (path' a a' b b')


_B↪∙_ : (X Y : Pointed ℓ-zero) → Type
X B↪∙ Y = Σ (⟨ X ⟩ → ⟨ Y ⟩) (λ f → ((y : ⟨ Y ⟩) → isSet (fiber f y)) × (f (pt X) ≡ pt Y))

∥_∥∙_ : Pointed ℓ-zero → ℕ → Pointed ℓ-zero
∥ (A , a) ∥∙ n = ∥ A ∥ n , ∣ a ∣ₕ

SubGroupπ₁ : (A : Pointed ℓ-zero) → Type₁
SubGroupπ₁ A∙ = Σ (Pointed ℓ-zero) (λ BG∙ → (BG∙ B↪∙ (∥ A∙ ∥∙ 3)) × isConnected' ⟨ BG∙ ⟩ × isGroupoid ⟨ BG∙ ⟩)

-- Useful when doing the "equivalence" proof
SubGroupπ₁' : Pointed ℓ-zero → Type₁
SubGroupπ₁' A = Σ (Σ (Pointed ℓ-zero) (λ X → ⟨ X ⟩ → ⟨ ∥ A ∥∙ 3 ⟩)) (λ (X , f) → (f (pt X) ≡ ∣ pt A ∣) × isConnected' ⟨ X ⟩ × isGroupoid ⟨ X ⟩ × ((a : ⟨ ∥ A ∥∙ 3 ⟩) → isSet(fiber f a)))

PCCovering₀ : (A : Pointed ℓ-zero) → Type₁
PCCovering₀ A = Σ (Covering₀ ⟨ A ⟩) λ C → ((Σ (C .Covering₀.B) λ c → C .Covering₀.f c ≡ pt A) × isConnected' (C .Covering₀.B))

PCCovering₀' : (A : Pointed ℓ-zero) → Type₁
PCCovering₀' A = Σ (Σ (Pointed ℓ-zero) (λ X → (⟨ X ⟩ → ⟨ A ⟩))) λ (X , f) → (f (pt X) ≡ pt A) × (isConnected' ⟨ X ⟩) × ((a : ⟨ A ⟩) → isSet (fiber f a))

