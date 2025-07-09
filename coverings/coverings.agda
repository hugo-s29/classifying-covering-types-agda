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

-- Useful when doing the "equivalence" proof
SubGroupπ₁' : Pointed ℓ-zero → Type₁
SubGroupπ₁' A = Σ (Σ (Pointed ℓ-zero) (λ X → ⟨ X ⟩ → ⟨ ∥ A ∥∙ 3 ⟩)) (λ (X , f) → (f (pt X) ≡ ∣ pt A ∣) × isConnected' ⟨ X ⟩ × isGroupoid ⟨ X ⟩ × ((a : ⟨ ∥ A ∥∙ 3 ⟩) → isSet(fiber f a)))

PCCovering₀ : (A : Pointed ℓ-zero) → Type₁
PCCovering₀ A = Σ (Covering₀ ⟨ A ⟩) λ C → ((Σ (C .Covering₀.B) λ c → C .Covering₀.f c ≡ pt A) × isConnected' (C .Covering₀.B))

PCCovering₀' : (A : Pointed ℓ-zero) → Type₁
PCCovering₀' A = Σ (Σ (Pointed ℓ-zero) (λ X → (⟨ X ⟩ → ⟨ A ⟩))) λ (X , f) → (f (pt X) ≡ pt A) × (isConnected' ⟨ X ⟩) × ((a : ⟨ A ⟩) → isSet (fiber f a))

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

  connectedCovering₀ : PCCovering₀' A∙
  connectedCovering₀ = ((X , (pt BG∙ , pt A∙ , Bi∙ .snd .snd)) , p) , refl , connected , p-isCov₀

module PCCovering₀→Subgroup (A∙ : Pointed ℓ-zero) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A∙) where
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

  subgroup : SubGroupπ₁' A∙
  subgroup = (((∥ X ∥ 3) , ∣ x ∣) , Bi∙ .fst) , Bi∙ .snd .snd , connected , isOfHLevelTrunc 3 , Bi∙ .snd .fst

module _ (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) where
  SubGroupπ₁'→PCCovering₀' : SubGroupπ₁' A → PCCovering₀' A
  SubGroupπ₁'→PCCovering₀' ((X , Bi) , Bi-⋆ , conX , _ , Bi-set) = Subgroup→PCCovering₀.connectedCovering₀ A X conA conX (Bi , Bi-set , Bi-⋆)

  SubGroupπ₁'←PCCovering₀' : PCCovering₀' A → SubGroupπ₁' A
  SubGroupπ₁'←PCCovering₀' = PCCovering₀→Subgroup.subgroup A

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

transport-Σ : ∀ {A : Type} {B C : A → Type} (x : Σ A B) (p : (a : A) → B a ≡ C a) → transport (λ i → Σ A (λ a → p a i)) x ≡ (fst x , transport (p (fst x)) (snd x))
transport-Σ {A = A} x@(a , b) p = fromPathP lem
  where
  lem : PathP (λ i → Σ A (λ a → p a i)) x (fst x , transport (p (fst x)) (snd x))
  lem = ΣPathP (refl , (transport-filler (p a) b))

toPathP-lemma : {A : Type} {B : A → Type} (a b : A) (x : B a) (y : B b) (q : a ≡ b) (p : subst B q x ≡ y) (i : I) → toPathP {A = λ i → B (q i)} {x = x} p i ≡ subst B (λ j → q (i ∧ j)) x
toPathP-lemma a b x y q p = {!!}

module LeftInv (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) (((BG , Bi), Bi-⋆ , conBG , grpBG , Bi-fib) : SubGroupπ₁' A) where

  Bi∙ : BG B↪∙ (∥ A ∥∙ 3)
  Bi∙ = Bi , Bi-fib , Bi-⋆

  t : ⟨ BG ⟩ → ∥ pullbackΣ Bi ∣_∣ ∥ 3
  t g = ∥-∥ₕ-elim
    {B = λ a → Bi g ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3}
    (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3)
    (λ a r → ∣ g , a , r ∣)
    (Bi g)
    refl

  s : ∥ pullbackΣ Bi ∣_∣ ∥ 3 → ⟨ BG ⟩
  s = ∥-∥ₕ-elim
    {B = λ _ → ⟨ BG ⟩}
    (λ _ → grpBG)
    (λ (g , a , r) → g)

  t∘s : (x : ∥ pullbackΣ Bi ∣_∣ ∥ 3) → t (s x) ≡ x
  t∘s = ∥-∥ₕ-elim
    {B = λ x → t (s x) ≡ x}
    (λ x → isOfHLevelTruncPath {y = x})
    (λ (g , a , r) → cong₂ (∥-∥ₕ-elim {B = λ a → Bi g ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ g , a , r ∣)) r (toPathP ( substInPathsL r refl ∙ lUnit r ⁻¹)))

  s∘t : (g : ⟨ BG ⟩) → s (t g) ≡ g
  s∘t g = ∥-∥ₕ-elim {B = λ a → (r : Bi g ≡ a) → s (∥-∥ₕ-elim {B = λ a → Bi g ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ g , a , r ∣) a r)  ≡ g}
    (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (grpBG _ _)) (λ _ _ → refl) (Bi g) refl

  ⟨BG⟩≅∥X∥ : ⟨ BG ⟩ ≅ (∥ pullbackΣ Bi ∣_∣ ∥ 3)
  ⟨BG⟩≅∥X∥ = iso t s t∘s s∘t

  ⟨BG⟩≡∥X∥ : ⟨ BG ⟩ ≡ ∥ pullbackΣ Bi ∣_∣ ∥ 3
  ⟨BG⟩≡∥X∥ = isoToPath ⟨BG⟩≅∥X∥

  ptBG≡∣x∣ : PathP (λ i → ⟨BG⟩≡∥X∥ i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣
  ptBG≡∣x∣ = toPathP (
      transport ⟨BG⟩≡∥X∥ (pt BG)
    ≡⟨ transportIsoToPath ⟨BG⟩≅∥X∥ (pt BG) ⟩
      ∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) (Bi (pt BG)) refl
    ≡⟨ cong₂ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣)) Bi-⋆ (toPathP ( substInPathsL Bi-⋆ refl ∙ lUnit _ ⁻¹)) ⟩
      ∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) ∣ pt A ∣ Bi-⋆
    ≡⟨⟩
      ∣ pt BG , pt A , Bi-⋆ ∣ ∎)

  ∥p∥ : ∥ pullbackΣ Bi ∣_∣ ∥ 3 → ∥ ⟨ A ⟩ ∥ 3
  ∥p∥ = ∥-∥ₕ-map (λ x → x .snd .fst)

  Bi≡∥p∥ : PathP (λ i → ⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3) Bi ∥p∥
  Bi≡∥p∥ = symP (subst (PathP (λ i → ⟨BG⟩≡∥X∥ (~ i) → ∥ ⟨ A ⟩ ∥ 3) ∥p∥) (funExt lemma) (funTypeTransp (λ X → X) (λ _ → ∥ ⟨ A ⟩ ∥ 3) (sym ⟨BG⟩≡∥X∥) ∥p∥)) where

    lemma : (g : ⟨ BG ⟩) → transport refl (∥p∥ (transport ⟨BG⟩≡∥X∥ g)) ≡ Bi g
    lemma g =
        transport refl (∥p∥ (transport ⟨BG⟩≡∥X∥ g))
      ≡⟨ transportRefl _ ⟩
        ∥p∥ (transport ⟨BG⟩≡∥X∥ g)
      ≡⟨ cong ∥p∥ (transportIsoToPath ⟨BG⟩≅∥X∥ g) ⟩
        ∥p∥ (t g)
      ≡⟨ ∥-∥ₕ-elim {B = λ x → ∥p∥ x ≡ Bi (s x)} (λ x → isOfHLevelTruncPath {x = ∥p∥ x}) (λ (_ , _ , q) → sym q) (t g) ⟩
        Bi (s (t g))
      ≡⟨ cong Bi (s∘t g) ⟩
        Bi g ∎

  Bi⋆≡refl' : subst (λ X → {!!}) ⟨BG⟩≡∥X∥ Bi-⋆ ≡ refl
  Bi⋆≡refl' = {!!}

  Bi⋆≡refl : PathP (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i) ≡ ∣ pt A ∣) Bi-⋆ refl
  Bi⋆≡refl = {!!}

  {-
      subst (λ x → x ≡ ∣ pt A ∣) (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) Bi-⋆
    ≡⟨ substInPathsR (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) Bi-⋆ ⟩
      (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) ⁻¹ ∙ Bi-⋆
    ≡⟨ cong (λ x → x ⁻¹ ∙ Bi-⋆) Bi⋆≡path ⟩
      Bi-⋆ ⁻¹ ∙ Bi-⋆
    ≡⟨ lCancel Bi-⋆ ⟩
      refl
  -}

  leftInv : SubGroupπ₁'←PCCovering₀' A conA (SubGroupπ₁'→PCCovering₀' A conA ((BG , Bi) , Bi-⋆ , conBG , grpBG , Bi-fib)) ≡ ((BG , Bi) , Bi-⋆ , conBG , grpBG , Bi-fib)
  leftInv = ΣPathP ((ΣPathP ((ΣPathP (⟨BG⟩≡∥X∥ , ptBG≡∣x∣)) , Bi≡∥p∥)) , ΣPathP ({!!} , toPathP (isProp× isConnected'IsProp (isProp× isPropIsGroupoid (isPropΠ (λ _ → isPropIsSet))) _ _))) ⁻¹

module RightInv (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x) , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where

  ∥p∥ : ∥ X ∥ 3 → ∥ ⟨ A ⟩ ∥ 3
  ∥p∥ = ∥-∥ₕ-map p

  X̃ = pullbackΣ {B = ⟨ A ⟩} ∥p∥ ∣_∣

  p̃ : X̃ → ⟨ A ⟩
  p̃ (_ , a , _) = a

  e : X → X̃
  e x = ∣ x ∣ , p x , refl

  e-fib : (a : ⟨ A ⟩) → fiber p a → fiber p̃ a
  e-fib _ (x , q) = (∣ x ∣ , p x , refl) , q

  e'-fib : (a : ⟨ A ⟩) → fiber p̃ a → fiber p a
  e'-fib a₀ ((x , a , q) , r) =
    ∥-∥ₕ-elim
      {B = λ x → (q : ∥p∥ x ≡ ∣ a ∣) → fiber p a₀}
      (λ _ → isGroupoidΠ (λ _ → isSet→isGroupoid (fib-set a₀)))
      (λ x q →
        ∥-∥ₕ-elim
        {B = λ _ → fiber p a₀}
        (λ _ → fib-set a₀)
        (λ q → x , q ∙ r)
        (transport (PathIdTrunc 2) q)
      )
      x q

  e'∘e : (a : ⟨ A ⟩) (x : X) (q : p x ≡ a) → e'-fib a (e-fib a (x , q)) ≡ (x , q)
  e'∘e a x q =
      ∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ r → x , r ∙ q) (transport (PathIdTrunc 2) refl)
    ≡⟨ cong (∥-∥ₕ-elim {B = λ _ → fiber p a} (λ _ → fib-set a) (λ r → x , r ∙ q)) (transportIsoToPath (PathIdTruncIso 2) refl ∙ transportRefl ∣ refl ∣) ⟩
      x , refl ∙ q
    ≡⟨ cong (λ q → x , q) (lUnit q ⁻¹) ⟩
      x , q ∎

  fibp̃-isSet : (a : ⟨ A ⟩) → isSet (fiber p̃ a)
  fibp̃-isSet a = Subgroup→PCCovering₀.p-isCov₀ A (∥ X , x ∥∙ 3) conA (PCCovering₀→Subgroup.connected A (((X , x) , p) , p⋆ , hypCon , fib-set)) (PCCovering₀→Subgroup.Bi∙ A (((X , x) , p) , (p⋆ , hypCon , fib-set))) a

  e∘e' : (a₀ : ⟨ A ⟩) (a : ⟨ A ⟩) (x : ∥ X ∥ 3) (q : ∥p∥ x ≡ ∣ a ∣) (r : a ≡ a₀) → e-fib a₀ (e'-fib a₀ ((x , a , q) , r)) ≡ ((x , a , q) , r)
  e∘e' a₀ a x q r =
    ∥-∥ₕ-elim
    {B = λ x → (q : ∥p∥ x ≡ ∣ a ∣) → e-fib a₀ (e'-fib a₀ ((x , a , q) , r)) ≡ ((x , a , q) , r)}
    (λ x → isGroupoidΠ (λ q → isSet→isGroupoid (isProp→isSet (fibp̃-isSet a₀ _ _))))
    (λ x q →
      subst (λ q → e-fib a₀ (e'-fib a₀ ((∣ x ∣ , a , q) , r)) ≡ ((∣ x ∣ , a , q) , r)) (transport⁻Transport (PathIdTrunc 2) q)
      (∥-∥ₕ-elim
        {B = λ q → e-fib a₀ (e'-fib a₀ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q) , r)) ≡ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) q), r)}
        (λ _ → isProp→isSet (fibp̃-isSet a₀ _ _))
        (λ q →
          J (λ a q → (r : a ≡ a₀) → e-fib a₀ (e'-fib a₀ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , r)) ≡ ((∣ x ∣ , a , transport⁻ (PathIdTrunc 2) ∣ q ∣) , r))
          (λ r →
            e-fib a₀ (e'-fib a₀ ((∣ x ∣ , p x , transport⁻ (PathIdTrunc 2) ∣ refl ∣) , r))
          ≡⟨⟩
            e-fib a₀ (∥-∥ₕ-elim {B = λ _ → fiber p a₀} (λ _ → fib-set a₀) (λ q → x , q ∙ r) (transport (PathIdTrunc 2) (transport⁻ (PathIdTrunc 2) ∣ refl ∣)))
          ≡⟨ cong (λ u → e-fib a₀ (∥-∥ₕ-elim {B = λ _ → fiber p a₀} (λ _ → fib-set a₀) (λ q → x , q ∙ r) u)) (transportTransport⁻ (PathIdTrunc 2) ∣ refl ∣) ⟩
            e-fib a₀ (x , refl ∙ r)
          ≡⟨⟩
            (∣ x ∣ , p x , refl) , refl ∙ r
          ≡⟨ ΣPathP (refl , lUnit r ⁻¹) ⟩
            (∣ x ∣ , p x , refl) , r
          ≡⟨ ΣPathP ((ΣPathP (refl , (ΣPathP (refl , ( transportIsoToPath⁻ (PathIdTruncIso 2) ∣ refl ∣ ⁻¹))))) , toPathP (transportRefl r)) ⟩
            (∣ x ∣ , p x , transport⁻ (PathIdTrunc 2) ∣ refl ∣) , r ∎
          ) q r
        ) (transport (PathIdTrunc 2) q))
    ) x q

  fibp≡fibp̃ : (a : ⟨ A ⟩) → fiber p a ≡ fiber p̃ a
  fibp≡fibp̃ a = isoToPath (iso (e-fib a) (e'-fib a) (λ x → e∘e' a (x .fst .snd .fst) (x .fst .fst) (x .fst .snd .snd) (x .snd)) λ x → e'∘e a (x .fst) (x .snd))

  X≡X̃ : X ≡ X̃
  X≡X̃ =
      X
    ≡⟨ ua (totalEquiv p) ⟩
      Σ ⟨ A ⟩ (fiber p)
    ≡⟨ Σ-cong-snd fibp≡fibp̃ ⟩
      Σ ⟨ A ⟩ (fiber p̃)
    ≡⟨ ua (totalEquiv p̃) ⁻¹ ⟩
      X̃ ∎


  transportX≡X̃ : (x : X) → transport X≡X̃ x ≡ e x
  transportX≡X̃ x =
      transport (ua (totalEquiv p) ∙ Σ-cong-snd fibp≡fibp̃ ∙ ua (totalEquiv p̃) ⁻¹ ∙ refl) x
    ≡⟨ transportComposite (ua (totalEquiv p)) (Σ-cong-snd fibp≡fibp̃ ∙ ua (totalEquiv p̃) ⁻¹ ∙ refl) x ⟩
      transport (Σ-cong-snd fibp≡fibp̃ ∙ ua (totalEquiv p̃) ⁻¹ ∙ refl) (transport (ua (totalEquiv p)) x)
    ≡⟨ transportComposite (Σ-cong-snd fibp≡fibp̃) (ua (totalEquiv p̃) ⁻¹ ∙ refl) (transport (ua (totalEquiv p)) x) ⟩
      transport (ua (totalEquiv p̃) ⁻¹ ∙ refl) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x))
    ≡⟨ transportComposite (ua (totalEquiv p̃) ⁻¹) refl (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x)) ⟩
      transport refl (transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x)))
    ≡⟨ transportRefl (transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x))) ⟩
      transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (transport (ua (totalEquiv p)) x))
    ≡⟨ cong (λ u → transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) u)) (uaβ (totalEquiv p) x) ⟩
      transport (ua (totalEquiv p̃) ⁻¹) (transport (Σ-cong-snd fibp≡fibp̃) (p x , x , refl))
    ≡⟨ cong (transport (ua (totalEquiv p̃) ⁻¹)) (transportRefl (p x , (∣ x ∣ , p x , refl) , refl)) ⟩
      transport (ua (totalEquiv p̃) ⁻¹) (p x , (∣ x ∣ , p x , refl) , refl)
    ≡⟨ ~uaβ (totalEquiv p̃) (p x , (∣ x ∣ , p x , refl) , refl) ⟩
      e x ∎

  x≡x̃ : PathP (λ i → X≡X̃ i) x (∣ x ∣ , pt A , cong ∣_∣ p⋆)
  x≡x̃ = toPathP (
      transport X≡X̃ x
    ≡⟨ transportX≡X̃ x ⟩
      ∣ x ∣ , p x , cong ∣_∣ refl
    ≡⟨ ΣPathP (refl , (ΣPathP (p⋆ , (toPathP lemma)))) ⟩
      ∣ x ∣ , pt A , cong ∣_∣ p⋆ ∎)
    where

    lemma : subst (λ a → ∣ p x ∣ ≡ ∣ a ∣) p⋆ refl ≡ cong ∣_∣ p⋆
    lemma = substInPaths (λ _ → ∣ p x ∣) ∣_∣ p⋆ refl ∙ lUnit _ ⁻¹ ∙ lUnit _ ⁻¹

  p≡p̃ : PathP (λ i → X≡X̃ i → ⟨ A ⟩) p p̃
  p≡p̃ = symP (transport (cong (λ p → PathP (λ i → X≡X̃ (~ i) → ⟨ A ⟩) p̃ p) (funExt lemma)) (funTypeTransp (λ X → X) (λ _ → ⟨ A ⟩) (sym X≡X̃) p̃ ))
    where

    lemma : (x : X) → transport refl (p̃ (transport X≡X̃ x)) ≡ p x
    lemma x =
        transport refl (p̃ (transport X≡X̃ x))
      ≡⟨ transportRefl (p̃ (transport X≡X̃ x)) ⟩
        p̃ (transport X≡X̃ x)
      ≡⟨ cong p̃ (transportX≡X̃ x) ⟩
        p̃ (e x)
      ≡⟨⟩
        p x ∎

  p⋆≡refl : PathP (λ i → p≡p̃ i (x≡x̃ i) ≡ pt A) p⋆ refl
  p⋆≡refl = {!!}

  rightInv : SubGroupπ₁'→PCCovering₀' A conA (SubGroupπ₁'←PCCovering₀' A conA (((X , x) , p) , p⋆ , hypCon , fib-set)) ≡ (((X , x) , p) , p⋆ , hypCon , fib-set)
  rightInv = ΣPathP ((ΣPathP ((ΣPathP (X≡X̃ , x≡x̃)) , p≡p̃)) , (ΣPathP ({!!} , toPathP (isProp× isConnected'IsProp (isPropΠ (λ _ → isPropIsSet)) _ _)))) ⁻¹

{-
module GaloisCorrespondance (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) where

  galois-correspondance≅' : SubGroupπ₁' A ≅ PCCovering₀' A
  galois-correspondance≅' ._≅_.fun = SubGroupπ₁'→PCCovering₀' A conA
  galois-correspondance≅' ._≅_.inv = SubGroupπ₁'←PCCovering₀' A conA
  galois-correspondance≅' ._≅_.rightInv x = {!!}
  galois-correspondance≅' ._≅_.leftInv = {!!}

  galois-correspondance' : SubGroupπ₁' A ≃ PCCovering₀' A
  galois-correspondance' = isoToEquiv galois-correspondance≅'
-}
