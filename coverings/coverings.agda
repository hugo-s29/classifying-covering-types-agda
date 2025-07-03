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
open import Pullback

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

module UniversalCovering (A∙ : Pointed ℓ-zero) (_ : isConnected' ⟨ A∙ ⟩) where
  A = ⟨ A∙ ⟩
  ⋆A = pt A∙

  Ã = Σ A (λ a → ∥ ⋆A ≡ a ∥ 2)

  1-connected : isConnected 3 Ã
  1-connected = ∣ ⋆A , ∣ refl ∣ ∣ , ∥-∥ₕ-elim {B = λ y → ∣ ⋆A , ∣ refl ∣ ∣ ≡ y} (λ y → isOfHLevelTruncPath {y = y})
    (λ (a , p) → transport⁻ (PathIdTrunc 2) (∥-∥ₕ-elim {B = λ p → ∥ (⋆A , ∣ refl ∣) ≡ (a , p) ∥ 2} (λ _ → isOfHLevelTrunc 2)
      (J (λ a p → ∥ (⋆A , ∣ refl ∣) ≡ (a , ∣ p ∣) ∥ 2) ∣ refl ∣) p))

  connected : isConnected' Ã
  connected = ∣ (⋆A , ∣ refl ∣) ∣₁ , lemma₂ where

    lemma₀ : (a b : A) (p : ⋆A ≡ a) (q : ⋆A ≡ b) → (a , ∣ p ∣) ≡ (b , ∣ q ∣)
    lemma₀ a b = J (λ a p → (q : ⋆A ≡ b) → (a , ∣ p ∣) ≡ (b , ∣ q ∣)) (J (λ b q → (⋆A , ∣ refl ∣) ≡ (b , ∣ q ∣)) refl)

    lemma₁ : (a : A) (p : ⋆A ≡ a) (y : Ã) → ∥ (a , ∣ p ∣) ≡ y ∥₁
    lemma₁ a p (b , q) = ∥-∥ₕ-elim {B = λ q → ∥ (a , ∣ p ∣) ≡ (b , q) ∥₁} (λ _ → isProp→isSet isPropPropTrunc) (λ q → ∣ lemma₀ a b p q ∣₁) q

    lemma₂ : (x y : Ã) → ∥ x ≡ y ∥₁
    lemma₂ (a , p) = ∥-∥ₕ-elim {B = λ p → (y : Ã) → ∥ (a , p) ≡ y ∥₁} (λ _ → isProp→isSet (isPropΠ (λ _ → isPropPropTrunc))) (lemma₁ a) p

_B↪∙_ : (X Y : Pointed ℓ-zero) → Type
X B↪∙ Y = Σ (⟨ X ⟩ → ⟨ Y ⟩) (λ f → ((y : ⟨ Y ⟩) → isSet (fiber f y)) × (f (pt X) ≡ pt Y))

∥_∥∙_ : Pointed ℓ-zero → ℕ → Pointed ℓ-zero
∥ (A , a) ∥∙ n = ∥ A ∥ n , ∣ a ∣ₕ

SubGroupπ₁ : (A : Pointed ℓ-zero) → Type₁
SubGroupπ₁ A∙ = Σ (Pointed ℓ-zero) (λ BG∙ → (BG∙ B↪∙ (∥ A∙ ∥∙ 3)) × isConnected' ⟨ BG∙ ⟩ × isGroupoid ⟨ BG∙ ⟩)

PCCovering₀ : (A : Pointed ℓ-zero) → Type₁
PCCovering₀ A = Σ (Covering₀ ⟨ A ⟩) λ C → ((Σ (C .Covering₀.B) λ c → C .Covering₀.f c ≡ pt A) × isConnected' (C .Covering₀.B))

module Subgroup→PCCovering₀ (A∙ BG∙ : Pointed ℓ-zero) (hyp-conA : isConnected' ⟨ A∙ ⟩ )
  (hyp-conBG : isConnected' ⟨ BG∙ ⟩) (Bi∙ : BG∙ B↪∙ (∥ A∙ ∥∙ 3)) where

  A = ⟨ A∙ ⟩

  BG = fst BG∙

  Bi : BG → ∥ A ∥ 3
  Bi = fst Bi∙

  X : Type
  X = pullbackΣ {C = ∥ A ∥ 3} Bi ∣_∣ -- This is written as "\|" not just | because | ≠ ∣ in Unicode

  p : X → A
  p = pullbackΣ-proj₂

  u : X → BG
  u = pullbackΣ-proj₁

  F : A → Type
  F a = Pullback p (pick a)

  F' : A → Type
  F' a = Pullback Bi (∣_∣ ∘ pick a)

  fib-p≡fib-Bi : (a : A) → fiber p a ≡ fiber Bi ∣ a ∣
  fib-p≡fib-Bi a =
      fiber p a
    ≡⟨ sym (Pullback-fiber₂ p (pick a)) ⟩
      F a
    ≡⟨ sym (PastingLemma-horizontal.pasting-lemma (pick a) ∣_∣ Bi) ⟩
      F' a
    ≡⟨ Pullback-fiber₂ Bi (∣_∣ ∘ pick a) ⟩
      fiber Bi ∣ a ∣ ∎

  isSet-fib-Bi : (a : A) → isSet (fiber Bi ∣ a ∣)
  isSet-fib-Bi a = Bi∙ .snd .fst ∣ a ∣

  p-isCov₀ : isCovering₀ p
  p-isCov₀ a = subst isSet (sym (fib-p≡fib-Bi a)) (isSet-fib-Bi a)

  subgroup→covering₀ : Covering₀ A
  subgroup→covering₀ = record { B = X ; f = p ; p = p-isCov₀ }

  X≡Σfibu : X ≡ Σ BG (fiber u)
  X≡Σfibu = ua (totalEquiv u)

  Ã : (x : ∥ A ∥ 3) → Type
  Ã x = Pullback {A = ⊤} (pick x) ∣_∣

  Ã≡fibu : (x : BG) → Ã (Bi x) ≡ fiber u x
  Ã≡fibu x =
      Pullback {A = ⊤} (Bi ∘ (pick x)) ∣_∣
    ≡⟨ PastingLemma-vertical.pasting-lemma (pick x) Bi ∣_∣ ⟩
      Pullback {A = ⊤} (pick x) u
    ≡⟨ Pullback-fiber₁ (pick x) u ⟩
      fiber u x ∎

  Ã-paths≡Ã-pullback : (a : A) → UniversalCovering.Ã (A , a) hyp-conA ≡ Pullback (pick ∣ a ∣) ∣_∣
  Ã-paths≡Ã-pullback a =
        Σ A (λ a' → ∥ a ≡ a' ∥ 2)
      ≡⟨ Σ-cong-snd (λ x → sym (PathIdTrunc 2)) ⟩
        Σ A (λ a' → ∣ a ∣ ≡ ∣ a' ∣)
      ≡⟨ Σ-cong-snd (λ x → isoToPath (iso sym sym (λ _ → refl) (λ _ → refl))) ⟩
        fiber ∣_∣ ∣ a ∣
      ≡⟨ Pullback-fiber₁ (pick ∣ a ∣) ∣_∣ ⁻¹ ⟩
        Pullback {A = ⊤} (pick ∣ a ∣) ∣_∣  ∎

  isConnected'Ã : (x : ∥ A ∥ 3) → isConnected' (Ã x)
  isConnected'Ã = ∥-∥ₕ-elim (λ x → isSet→isGroupoid (isProp→isSet isConnected'IsProp)) λ a → isConnected'Ã∣a∣ a where

    isConnected'Ã∣a∣ : (a : A) → isConnected' (Ã ∣ a ∣)
    isConnected'Ã∣a∣ a = subst isConnected' (Ã-paths≡Ã-pullback a) (UniversalCovering.connected (A , a) hyp-conA)

  isConnected'-fibu : (x : BG) → isConnected' (fiber u x)
  isConnected'-fibu x = subst isConnected' (Ã≡fibu x) (isConnected'Ã (Bi x))

  connected : isConnected' X
  connected = subst isConnected' (sym X≡Σfibu) (isConnected'Σ hyp-conBG isConnected'-fibu)

  connectedCovering₀ : PCCovering₀ A∙
  connectedCovering₀ = subgroup→covering₀ , ((pt BG∙ , pt A∙ , Bi∙ .snd .snd) , refl) , connected

module PCCovering₀→Subgroup (A∙ : Pointed ℓ-zero) ((record { B = X ; f = p ; p = fib-set } , (x , p⋆) , hypCon) : PCCovering₀ A∙) where
  A : Type
  A = ⟨ A∙ ⟩

  Bi : (∥ X ∥ 3) → (∥ A ∥ 3)
  Bi = ∥-∥ₕ-map p

  --- F --> X --> ∥ X ∥
  --- | ⌟   |       |
  --- v     v       v
  --- 1 --> A --> ∥ A ∥

  fib-trunc-lemma : (a : A) → fiber p a ≡ fiber Bi ∣ a ∣
  fib-trunc-lemma a = isoToPath (iso to of s r) where

    to : fiber p a → fiber Bi ∣ a ∣
    to (x , q) = ∣ x ∣ , (transport⁻ (PathIdTrunc 2) ∣ q ∣)

    of : fiber Bi ∣ a ∣ → fiber p a
    of (x , q) = ∥-∥ₕ-elim {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a} (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a)))
       (λ x → λ (q : ∣ p x ∣ ≡ ∣ a ∣) → ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) q)) x q

    s : section to of
    s (x , q) = ΣPathTransport→PathΣ (to (of (x , q))) (x , q) (l₁ x q , l₂) where

      arg₁ : (x : ∥ X ∥ 3) → Bi x ≡ ∣ a ∣ → ∥ X ∥ 3
      arg₁ x q = ∣ ∥-∥ₕ-elim {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a} (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a)))
       (λ x → λ (q : ∣ p x ∣ ≡ ∣ a ∣) → ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) q)) x q .fst ∣

      l₁' : (x : X) (q : ∥ p x ≡ a ∥ 2) → Path (∥ X ∥ 3) ∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) q .fst ∣ ∣ x ∣
      l₁' x = ∥-∥ₕ-elim {B = λ q → Path (∥ X ∥ 3) ∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) q .fst ∣ ∣ x ∣}
              (λ q → subst⁻ isSet (PathIdTrunc 2) (isOfHLevelTrunc 2)) λ _ → refl

      l₁ : (x : ∥ X ∥ 3) (q : Bi x ≡ ∣ a ∣) → arg₁ x q ≡ x
      l₁ x q = ∥-∥ₕ-elim {B = λ x → ∀ q → arg₁ x q ≡ x}
        (λ x → isGroupoidΠ (λ q → isOfHLevelTruncPath {x = arg₁ x q} {y = x})) (λ x q → l₁' x (transport (PathIdTrunc 2) q)) x q

      arg₂ : (x : ∥ X ∥ 3) → Bi x ≡ ∣ a ∣ → Bi x ≡ ∣ a ∣
      arg₂ x q = subst (λ x → Bi x ≡ ∣ a ∣) (l₁ x q) (transport⁻ (PathIdTrunc 2) ∣ ∥-∥ₕ-elim {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a}
        (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a))) (λ x → λ (q : ∣ p x ∣ ≡ ∣ a ∣) → ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) q)) x q .snd ∣)

      l₂' : (x : ∥ X ∥ 3) (q : Bi x ≡ ∣ a ∣) → isGroupoid (arg₂ x q ≡ q)
      l₂' x q = isOfHLevelSuc 3 (isOfHLevelTruncPath {n = 3}) (arg₂ x q) q

      l₂'' : (x : X) (q : ∥ p x ≡ a ∥ 2) → arg₂ ∣ x ∣ (transport⁻ (PathIdTrunc 2) q) ≡ (transport⁻ (PathIdTrunc 2) q)
      l₂'' x = ∥-∥ₕ-elim {B = λ q → arg₂ ∣ x ∣ (transport⁻ (PathIdTrunc 2) q) ≡ (transport⁻ (PathIdTrunc 2) q)} (λ _ → isOfHLevelTruncPath {n = 3} _ _) (λ q →
          subst (λ x → Bi x ≡ ∣ a ∣) (l₁ ∣ x ∣ (transport⁻ (PathIdTrunc 2) ∣ q ∣)) (transport⁻ (PathIdTrunc 2) (
            ∣
                (∥-∥ₕ-elim
                {B = λ x → Bi x ≡ ∣ a ∣ → fiber p a}
                (λ _ → isSet→isGroupoid (isSetΠ (λ _ → fib-set a)))
                (λ x q →
                   ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q)
                   (transport (PathIdTrunc 2) q))
                ∣ x ∣ (transport⁻ (PathIdTrunc 2) ∣ q ∣) .snd)
             ∣
            ))
        ≡⟨⟩
          subst (λ x → Bi x ≡ ∣ a ∣) (l₁' x (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ q ∣))) (transport⁻ (PathIdTrunc 2) (
            ∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ q ∣)) .snd ∣))
        ≡⟨ cong (λ u → subst (λ x → Bi x ≡ ∣ a ∣) (l₁' x u) (transport⁻ (PathIdTrunc 2) (∣ ∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q) u .snd ∣))) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣) ⟩
          subst (λ x → Bi x ≡ ∣ a ∣) (l₁' x ∣ q ∣) (transport⁻ (PathIdTrunc 2) ∣ q ∣)
        ≡⟨⟩
          subst {x = ∣ x ∣} (λ x → Bi x ≡ ∣ a ∣) refl (transport⁻ (PathIdTrunc 2) ∣ q ∣)
        ≡⟨ transportRefl (transport⁻ (PathIdTrunc 2) ∣ q ∣) ⟩
          transport⁻ (PathIdTrunc 2) ∣ q ∣ ∎
        )

      l₂ : arg₂ x q ≡ q
      l₂ = ∥-∥ₕ-elim {B = λ x → (q : Bi x ≡ ∣ a ∣) → arg₂ x q ≡ q} (λ x → isGroupoidΠ (l₂' x)) (λ x q →
          subst (λ q → arg₂ ∣ x ∣ q ≡ q) (transport⁻Transport (PathIdTrunc 2) q) (l₂'' x (transport (PathIdTrunc 2) q))
        ) x q

    r : retract to of
    r (x , q) = cong (∥-∥ₕ-elim (λ _ → fib-set a) (λ q → x , q)) (transportTransport⁻ (PathIdTrunc 2) ∣ q ∣)

  Bi∙ : (∥ (X , x) ∥∙ 3) B↪∙ (∥ A∙ ∥∙ 3)
  Bi∙ = Bi ,  ∥-∥ₕ-elim (λ _ → isSet→isGroupoid (isProp→isSet isPropIsSet)) (λ a → subst isSet (fib-trunc-lemma a) (fib-set a)) , cong ∣_∣ p⋆

  connected : isConnected' (∥ X ∥ 3)
  connected = ∣ ∣ x ∣ ∣₁ , ∥-∥ₕ-elim2 (λ _ _ → isSet→isGroupoid (isProp→isSet isPropPropTrunc)) λ a b → ∥-∥-elim (λ _ → isPropPropTrunc) (∣_∣₁ ∘ cong ∣_∣) (hypCon .snd a b)

  subgroup : SubGroupπ₁ A∙
  subgroup = ((∥ X ∥ 3) , ∣ x ∣) , Bi∙ , connected , isOfHLevelTrunc 3

module _ (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) where
  SubGroupπ₁→PCCovering₀ : SubGroupπ₁ A → PCCovering₀ A
  SubGroupπ₁→PCCovering₀ (BG , Bi , conBG , grpBG) = Subgroup→PCCovering₀.connectedCovering₀ A BG conA conBG Bi

  SubGroupπ₁←PCCovering₀ : PCCovering₀ A → SubGroupπ₁ A
  SubGroupπ₁←PCCovering₀ = PCCovering₀→Subgroup.subgroup A

is-1-connected-iso : {A B : Type} (f : A → B) → isConnectedFun 3 f → (∥ A ∥ 3) ≅ (∥ B ∥ 3)
is-1-connected-iso f h ._≅_.fun = ∥-∥ₕ-map f
is-1-connected-iso f h ._≅_.inv = ∥-∥ₕ-elim (λ _ → isOfHLevelTrunc 3) λ b → ∥-∥ₕ-map fst (h b .fst)
is-1-connected-iso {B = B} f h ._≅_.rightInv = ∥-∥ₕ-elim (λ x → isOfHLevelTruncPath {y = x}) lemma where
  lemma : (b : B) → ∥-∥ₕ-map f (∥-∥ₕ-map fst (h b .fst)) ≡ ∣ b ∣
  lemma b = ∥-∥ₕ-elim (λ x → isOfHLevelTruncPath {x = ∥-∥ₕ-map f (∥-∥ₕ-map fst x)}) (λ (_ , p) → cong ∣_∣ p) (h b .fst)
is-1-connected-iso {A = A} f h ._≅_.leftInv = ∥-∥ₕ-elim (λ x → isOfHLevelTruncPath {y = x}) lemma where
  lemma : (a : A) → ∥-∥ₕ-map fst (h (f a) .fst) ≡ ∣ a ∣
  lemma a = cong (∥-∥ₕ-map fst) (h (f a) .snd ∣ a , refl ∣)

is-1-connected-equiv : {A B : Type} (f : A → B) → isConnectedFun 3 f → (∥ A ∥ 3) ≃ (∥ B ∥ 3)
is-1-connected-equiv f h = isoToEquiv (is-1-connected-iso f h)

transport-fun : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'} (p : A ≡ B) (f : A → C) (g : B → C) → (∀ x → f x ≡ g (transport p x)) → subst (λ A' → A' → C) p f ≡ g
transport-fun {B = B} {C = C} p f =
  J (λ B p → (g : B → C) → (∀ x → f x ≡ g (transport p x)) → subst (λ X → X → C) p f ≡ g )
  (λ g h → transportRefl f ∙ funExt (λ x → (h x) ∙ (cong g (transportRefl x)))) p

transport-fun⁻ : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'} (p : A ≡ B) (f : A → C) (g : B → C) → subst (λ A' → A' → C) p f ≡ g → ∀ x → f x ≡ g (transport p x)
transport-fun⁻ {B = B} {C = C} p f =
  J (λ B p → (g : B → C) → subst (λ X → X → C) p f ≡ g → ∀ x → f x ≡ g (transport p x))
  (λ g u x → funExt⁻ (substRefl {B = λ X → X → C} f ⁻¹ ∙ u) x ∙ cong g (transportRefl x ⁻¹)) p


module LeftInv (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((BG , Bi , conBG , grpBG) : SubGroupπ₁ A) where

  is-1-connected-Ã : (x : ∥ ⟨ A ⟩ ∥ 3) → isConnected 3 (Subgroup→PCCovering₀.Ã A BG conA conBG Bi x)
  is-1-connected-Ã = ∥-∥ₕ-elim (λ _ → isSet→isGroupoid (isProp→isSet isPropIsContr)) is-1-connected-Ã∣a∣ where

    is-1-connected-Ã∣a∣ : (a : ⟨ A ⟩) → isConnected 3 (Subgroup→PCCovering₀.Ã A BG conA conBG Bi ∣ a ∣)
    is-1-connected-Ã∣a∣ a = subst (isConnected 3) (Subgroup→PCCovering₀.Ã-paths≡Ã-pullback A BG conA conBG Bi a) (UniversalCovering.1-connected (⟨ A ⟩ , a) conA)

  u-1-connected : isConnectedFun 3 (fst {A = ⟨ BG ⟩} {B = λ g → Σ ⟨ A ⟩ λ a → Bi .fst g ≡ ∣ a ∣})
  u-1-connected g = subst (isConnected 3) (Subgroup→PCCovering₀.Ã≡fibu A BG conA conBG Bi g) (is-1-connected-Ã (Bi .fst g))

  lemma₁ : ∥ pullbackΣ (fst Bi) ∣_∣ , pt BG , pt A , Bi .snd .snd ∥∙ 3 ≡ BG
  lemma₁ = ΣPathTransport→PathΣ _ _ (isoToPath (is-1-connected-iso fst u-1-connected) ∙ truncIdempotent 3 grpBG , (
      transport (isoToPath (is-1-connected-iso fst u-1-connected) ∙ truncIdempotent 3 grpBG) ∣ pt BG , pt A , Bi .snd .snd ∣
    ≡⟨ transportComposite (isoToPath (is-1-connected-iso fst u-1-connected)) (truncIdempotent 3 grpBG) ∣ pt BG , pt A , Bi .snd .snd ∣ ⟩
      transport (truncIdempotent 3 grpBG) (transport (isoToPath (is-1-connected-iso fst u-1-connected)) ∣ pt BG , pt A , Bi .snd .snd ∣)
    ≡⟨ cong (transport (truncIdempotent 3 grpBG)) (transportIsoToPath (is-1-connected-iso fst u-1-connected) ∣ pt BG , pt A , Bi .snd .snd ∣) ⟩
      transport (truncIdempotent 3 grpBG) ∣ snd BG ∣
    ≡⟨ transportIsoToPath (truncIdempotentIso 3 grpBG) ∣ snd BG ∣ ⟩
      snd BG ∎
    ))

  roundtrip : SubGroupπ₁ A
  roundtrip = SubGroupπ₁←PCCovering₀ A conA (SubGroupπ₁→PCCovering₀ A conA (BG , Bi , conBG , grpBG))

  subst-fst : ∀ {ℓ} → {A : Type ℓ} (f : A → Type) (g : (x : A) → f x → Type) (x y : A) (p : x ≡ y) (u : Σ (f x) (g x)) → fst (subst (λ x → Σ (f x) (g x)) p u) ≡ subst f p (fst u)
  subst-fst f g x _ = J (λ y p → (u : Σ (f x) (g x)) → fst (subst (λ x → Σ (f x) (g x)) p u) ≡ subst f p (fst u)) λ u → cong fst (substRefl {B = (λ x → Σ (f x) (g x))} u) ∙ substRefl {B = f} (fst u) ⁻¹

  {-
  subst-snd : ∀ {ℓ} → {A : Type ℓ} (f : A → Type) (g : (x : A) → f x → Type) (x y : A) (p : x ≡ y) (u : Σ (f x) (g x)) → snd (subst (λ x → Σ (f x) (g x)) p u) ≡ subst (λ x → g x (fst u)) p (snd u)
  subst-snd f g x _ = J (λ y p → (u : Σ (f x) (g x)) → snd (subst (λ x → Σ (f x) (g x)) p u) ≡ subst g p (snd u)) λ u → cong snd (substRefl {B = (λ x → Σ (f x) (g x))} u) ∙ substRefl {B = g} (snd u) ⁻¹
  -}

  lemma₂ : subst (λ BG → (BG B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG ⟩ × isGroupoid ⟨ BG ⟩) lemma₁ (roundtrip .snd) ≡ (Bi , conBG , grpBG)
  lemma₂ = ΣPathP (lemma₂-a' , ΣPathP ({!!} , {!!})) where

    ∥p∥ : ∥ pullbackΣ (fst Bi) ∣_∣ ∥ 3 → ∥ ⟨ A ⟩ ∥ 3
    ∥p∥ = ∥-∥ₕ-map λ x → x .snd .fst

    lemma₂-a : fst (fst (subst (λ BG → (BG B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG ⟩ × isGroupoid ⟨ BG ⟩) lemma₁ (roundtrip .snd))) ≡ fst Bi
    lemma₂-a = transport-fun (cong ⟨_⟩ lemma₁) (roundtrip .snd .fst .fst) (Bi .fst) λ x → core-lemma₂-a x ⁻¹ where

      core-lemma₂-a : (x : ∥ pullbackΣ (fst Bi) ∣_∣ ∥ 3) → Bi .fst (transport (cong fst lemma₁) x) ≡ ∥p∥ x
      core-lemma₂-a = ∥-∥ₕ-elim (λ x → isOfHLevelTruncPath {y = ∥p∥ x}) λ x →
          Bi .fst (transport (isoToPath (is-1-connected-iso fst u-1-connected) ∙ truncIdempotent 3 grpBG) ∣ x ∣)
        ≡⟨ cong (Bi .fst) (transportComposite (isoToPath (is-1-connected-iso fst u-1-connected)) (truncIdempotent 3 grpBG) ∣ x ∣) ⟩
          Bi .fst (transport (truncIdempotent 3 grpBG) (transport (isoToPath (is-1-connected-iso fst u-1-connected)) ∣ x ∣))
        ≡⟨ cong (λ a → Bi .fst (transport (truncIdempotent 3 grpBG) a)) (transportIsoToPath (is-1-connected-iso fst u-1-connected) ∣ x ∣) ⟩
          Bi .fst (transport (truncIdempotent 3 grpBG) ∣ fst x ∣)
        ≡⟨ cong (Bi .fst) (transportIsoToPath (truncIdempotentIso 3 grpBG) ∣ fst x ∣) ⟩
          Bi .fst (fst x)
        ≡⟨ x .snd .snd ⟩
          ∣ x .snd .fst ∣ ∎

    lemma₂-a'' : fst (subst (λ f → ((y : ⟨ ∥ A ∥∙ 3 ⟩) → isSet (fiber f y)) × (f (pt BG) ≡ pt (∥ A ∥∙ 3))) lemma₂-a (snd (fst (subst (λ BG₁ → (BG₁ B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG₁ ⟩ × isGroupoid ⟨ BG₁ ⟩) lemma₁ (roundtrip .snd))))) ≡ fst (snd Bi)
    lemma₂-a'' =
        fst (subst (λ f → ((y : ⟨ ∥ A ∥∙ 3 ⟩) → isSet (fiber f y)) × (f (pt BG) ≡ pt (∥ A ∥∙ 3))) lemma₂-a (snd (fst (subst (λ BG₁ → (BG₁ B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG₁ ⟩ × isGroupoid ⟨ BG₁ ⟩) lemma₁ (roundtrip .snd)))))
      ≡⟨ cong (λ u → fst (subst (λ f → ((y : ⟨ ∥ A ∥∙ 3 ⟩) → isSet (fiber f y)) × (f (pt BG) ≡ pt (∥ A ∥∙ 3))) lemma₂-a u)) lemma₂-a''₃ ⟩
        fst (subst (λ f → ((y : ⟨ ∥ A ∥∙ 3 ⟩) → isSet (fiber f y)) × (f (pt BG) ≡ pt (∥ A ∥∙ 3))) lemma₂-a (lemma₂-a''₁ , lemma₂-a''₂))
      ≡⟨ subst-fst (λ f → (y : ⟨ ∥ A ∥∙ 3 ⟩) → isSet (fiber f y)) (λ f _ → f (pt BG) ≡ pt (∥ A ∥∙ 3)) _ (fst Bi) lemma₂-a (lemma₂-a''₁ , lemma₂-a''₂) ⟩
        subst (λ f → (y : ⟨ ∥ A ∥∙ 3 ⟩) → isSet (fiber f y)) lemma₂-a lemma₂-a''₁
      ≡⟨ {!!} ⟩
        fst (snd Bi) ∎ where

      lemma₂-a''₁ : (y : ⟨ ∥ A ∥∙ 3 ⟩) → isSet (fiber (fst (fst (subst (λ BG₁ → (BG₁ B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG₁ ⟩ × isGroupoid ⟨ BG₁ ⟩) lemma₁ (roundtrip .snd)))) y)
      lemma₂-a''₁ y = subst isSet (
          fiber (fst Bi) y
        ≡⟨ cong (λ f → fiber f y) (lemma₂-a ⁻¹) ⟩
          fiber (fst (fst (subst (λ BG₁ → (BG₁ B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG₁ ⟩ × isGroupoid ⟨ BG₁ ⟩) lemma₁ (roundtrip .snd)))) y ∎
        ) (Bi .snd .fst y)

      lemma₂-a''₂ : fst (fst (subst (λ BG₁ → (BG₁ B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG₁ ⟩ × isGroupoid ⟨ BG₁ ⟩) lemma₁ (roundtrip .snd))) (pt BG) ≡ pt (∥ A ∥∙ 3)
      lemma₂-a''₂ =
          fst (fst (subst (λ BG₁ → (BG₁ B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG₁ ⟩ × isGroupoid ⟨ BG₁ ⟩) lemma₁ (roundtrip .snd))) (pt BG)
        ≡⟨ funExt⁻ lemma₂-a (pt BG) ⟩
          fst Bi (pt BG)
        ≡⟨ Bi .snd .snd ⟩
          pt (∥ A ∥∙ 3) ∎


      lemma₂-a''₃ : snd (fst (subst (λ BG₁ → (BG₁ B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG₁ ⟩ × isGroupoid ⟨ BG₁ ⟩) lemma₁ (roundtrip .snd))) ≡ (lemma₂-a''₁ , lemma₂-a''₂)
      lemma₂-a''₃ = {!!}


    lemma₂-a' : fst (subst (λ BG → (BG B↪∙ (∥ A ∥∙ 3)) × isConnected' ⟨ BG ⟩ × isGroupoid ⟨ BG ⟩) lemma₁ (roundtrip .snd)) ≡ Bi
    lemma₂-a' = ΣPathP (lemma₂-a , toPathP (ΣPathP (lemma₂-a'' , {!!})))

  leftinv : roundtrip ≡ (BG , Bi , conBG , grpBG)
  leftinv = ΣPathP (lemma₁ , ΣPathP ({!!} , {!!}))


module GaloisCorrespondance (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) where

  galois-correspondance≅ : SubGroupπ₁ A ≅ PCCovering₀ A
  galois-correspondance≅ ._≅_.fun = SubGroupπ₁→PCCovering₀ A conA
  galois-correspondance≅ ._≅_.inv = SubGroupπ₁←PCCovering₀ A conA
  galois-correspondance≅ ._≅_.rightInv x = {!!}
  galois-correspondance≅ ._≅_.leftInv = {!!}

  galois-correspondance : SubGroupπ₁ A ≃ PCCovering₀ A
  galois-correspondance = isoToEquiv galois-correspondance≅
