open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.Sigma hiding (_×_)
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
open import Cubical.HITs.Truncation renaming (rec to ∥-∥ₕ-rec ; map to ∥-∥ₕ-map ; elim to ∥-∥ₕ-elim)
open import Cubical.HITs.SetTruncation renaming (rec to ∥-∥₂-rec ; map to ∥-∥₂-map ; elim to ∥-∥₂-elim)
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥-∥-rec ; map to ∥-∥-map ; map2 to ∥-∥-map2 ; elim to ∥-∥-elim)
open import Cubical.Homotopy.Connected
open import Cubical.WildCat.Base
open import Pullback

cong-fun : {A B : Type} (f g : A → B) (p : f ≡ g) (x : A) → f x ≡ g x
cong-fun f _ p x = J (λ g' _ → f x ≡ g' x) refl p

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

UniversalCovering₀ : (A : Type) → Type₁
UniversalCovering₀ A = Σ (Covering₀ A) (λ Cᵤ → (C : Covering₀ A) → Cᵤ →Cov₀ C)

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
isConnected' A = Σ A (λ a → ∀ b → ∥ a ≡ b ∥₁)

isConnected'Σ : {A : Type} {B : A → Type} → isConnected' A → (∀ x → isConnected' (B x)) → isConnected' (Σ A B)
isConnected'Σ {A} {B} (⋆A , hA) hB = (⋆A , ⋆B) , λ b → Σ∥-∥₁ (path b) where
  ⋆B : B ⋆A
  ⋆B = hB ⋆A .fst

  Σ∥-∥₁ : {x y : Σ A B} → ∥ (ΣPathTransport x y) ∥₁ → ∥ x ≡ y ∥₁
  Σ∥-∥₁ {x} {y} = ∥-∥-map  (ΣPathTransport→PathΣ x y)

  path' : ((a , b) : Σ A B) → ∥ ∥ Σ (⋆A ≡ a) (λ p → subst B p ⋆B ≡ b) ∥₁ ∥₁
  path' (a , b) =
    let (⋆a , hB') = hB a in
    ∥-∥-map (λ p →
      ∥-∥-map2 (λ pu pb → p , (pu ⁻¹ ∙ pb)) (hB' (subst B p ⋆B)) (hB' b)
    ) (hA a)

  path : ((a , b) : Σ A B) → ∥ Σ (⋆A ≡ a) (λ p → subst B p ⋆B ≡ b) ∥₁
  path x = transport (propTruncIdempotent isPropPropTrunc) (path' x)

isConnected'IsProp : {A : Type} → isProp (isConnected' A)
isConnected'IsProp = {! !} -- No idea where to start :(  (I wanted to make the equivalence with the isConnected 2 A, but it seems to be way harder than I thought)...

module UniversalCovering (A∙ : Pointed ℓ-zero) ((⋆A' , conA) : isConnected' ⟨ A∙ ⟩) where
  A = ⟨ A∙ ⟩
  ⋆A = pt A∙

  Ã = Σ A (λ a → ∥ ⋆A ≡ a ∥ 2)

  connected : isConnected' Ã -- propTrunc≡Trunc2... that's a fabulous name... completely wrong though
  connected = (⋆A , ∣ refl ∣) , λ (a , p) → ∥-∥ₕ-elim {B = λ p → ∥ (⋆A , ∣ refl ∣) ≡ (a , p) ∥₁} (λ _ → isProp→isSet isPropPropTrunc) (λ p →
      J (λ a p → ∥ Path Ã (⋆A , ∣ refl ∣) (a , ∣ p ∣) ∥₁) ∣ refl ∣₁ p
    ) p

module Subgroup→ConnectedCovering₀ (A∙ BG∙ : Pointed ℓ-zero) (hyp-conA : isConnected' ⟨ A∙ ⟩ )
  (hyp-conBG : isConnected' ⟨ BG∙ ⟩) (Bi∙ : ⟨ BG∙ ⟩ ↪ (∥ ⟨ A∙ ⟩ ∥ 3)) where

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

  pick : {W : Type} (a : W) → ⊤ → W
  pick x tt = x

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
  isSet-fib-Bi a = isProp→isSet (isEmbedding→hasPropFibers (Bi∙ .snd) ∣ a ∣)

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

  isConnected'Ã : (x : ∥ A ∥ 3) → isConnected' (Ã x)
  isConnected'Ã = ∥-∥ₕ-elim (λ x → isSet→isGroupoid (isProp→isSet isConnected'IsProp)) λ a → isConnected'Ã∣a∣ a where

    isConnected'Ã∣a∣ : (a : A) → isConnected' (Ã ∣ a ∣)
    isConnected'Ã∣a∣ a = subst isConnected' (
        Σ A (λ a' → ∥ a ≡ a' ∥ 2)
      ≡⟨ Σ-cong-snd (λ x → sym (PathIdTrunc 2)) ⟩
        Σ A (λ a' → ∣ a ∣ ≡ ∣ a' ∣)
      ≡⟨ Σ-cong-snd (λ x → isoToPath (iso sym sym (λ _ → refl) (λ _ → refl))) ⟩
        fiber ∣_∣ ∣ a ∣
      ≡⟨ Pullback-fiber₁ (pick ∣ a ∣) ∣_∣ ⁻¹ ⟩
        Pullback {A = ⊤} (pick ∣ a ∣) ∣_∣  ∎
      ) (UniversalCovering.connected (A , a) hyp-conA)

  isConnected'-fibu : (x : BG) → isConnected' (fiber u x)
  isConnected'-fibu x = subst isConnected' (Ã≡fibu x) (isConnected'Ã (Bi x))

  connected : isConnected' X
  connected = subst isConnected' (sym X≡Σfibu) (isConnected'Σ hyp-conBG isConnected'-fibu)

module ConnectedCovering₀→Subgroup (A∙ : Pointed ℓ-zero) ((record { B = X ; f = p ; p = fib-set }) : Covering₀ ⟨ A∙ ⟩) where
  A : Type
  A = ⟨ A∙ ⟩

  Bi : ∥ X ∥ 3 → ∥ A ∥ 3
  Bi = ∥-∥ₕ-map p

  Bi-embedding : isEmbedding Bi
  Bi-embedding = hasPropFibers→isEmbedding {!!}
