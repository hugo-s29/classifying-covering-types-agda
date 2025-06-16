open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

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

subst-sym : {A : Type} {B : A → Type} {x y : A} (p : x ≡ y) (u : B x) → subst B (sym p) (subst B p u) ≡ u
subst-sym {A} {B} p u = J (λ _ q → subst B (sym q) (subst B q u) ≡ u) (
      subst B (λ i → refl (~ i)) (subst B refl u)
    ≡⟨ cong (subst B (λ i → refl (~ i))) (JRefl (λ a _ → a) u) ⟩
      subst B (λ i → refl (~ i)) u
    ≡⟨ JRefl (λ a _ → a) u ⟩
      u ∎
  ) p


Σ←Covering₀ : {A : Type} → Covering₀ A → Σ Type (λ B → Σ (B → A) isCovering₀)
Σ←Covering₀ record { B = B ; f = f ; p = p } = B , f , p

Σ→Covering₀ : {A : Type} → Σ Type (λ B → Σ (B → A) isCovering₀) → Covering₀ A
Σ→Covering₀ (B , f , p) = record { B = B ; f = f ; p = p }

Σ≅Covering₀ : {A : Type} → Σ Type (λ B → Σ (B → A) isCovering₀) ≅ Covering₀ A
Σ≅Covering₀ {A} = iso Σ→Covering₀ Σ←Covering₀ s r where
  s : section Σ→Covering₀ Σ←Covering₀
  s x = refl

  r : retract Σ→Covering₀ Σ←Covering₀
  r x = refl

_∘_ : {A B C : Type₁} → (B → C) → (A → B) → (A → C)
(f ∘ g) z = f (g z)

retract∘≅ : {A B C : Type₁} (f : A → B) (g : B → A) (i : A ≅ C) → retract (f ∘ (_≅_.inv i)) ((_≅_.fun i) ∘ g) → retract f g
retract∘≅ f g i h x =
  let inv = _≅_.inv i in
  let fun = _≅_.fun i in
    g (f x)
  ≡⟨ cong g (cong f (sym (_≅_.leftInv i x))) ⟩
    g (f (inv (fun x)))
  ≡⟨ sym (_≅_.leftInv i _) ⟩
    inv (fun (g (f (inv (fun x)))))
  ≡⟨ cong inv (h (fun x)) ⟩
    inv (fun x)
  ≡⟨ _≅_.leftInv i x ⟩
    x ∎

Covering₀A≅A→Set : {A : Type} → Covering₀ A ≅ (A → Set)
Covering₀A≅A→Set {A} = iso Covering₀A→A→Set Covering₀A←A→Set Covering₀A≅A→Set-section Covering₀A≅A→Set-retract where

  Covering₀A→A→Set : Covering₀ A → A → Set
  Covering₀A→A→Set record { B = B ; f = f ; p = p } x = (fib f x) , (p x)

  fib≅h : {h : A → Set} (y : A) → fib {Σ A (λ x → h x .fst)} {A} fst y ≅ h y .fst
  fib≅h {h} y = iso fib→h fib←h fib≅h-section fib≅h-retract where

    fib→h : fib fst y → h y .fst
    fib→h ((y' , u) , p) = subst (λ x → h x .fst) p u

    fib←h : h y .fst → fib fst y
    fib←h C = (y , C) , refl

    fib≅h-retract : retract fib→h fib←h
    fib≅h-retract ((y₀ , u) , p) = ΣPathTransport→PathΣ _ _ (map₁ , map₂) where

      map₁ : fst (fib←h (fib→h ((y₀ , u) , p))) ≡ (y₀ , u)
      map₁ = ΣPathTransport→PathΣ _ _ (map₁-a , map₁-b) where

        map₁-a : fst (fst (fib←h (fib→h ((y₀ , u) , p)))) ≡ y₀
        map₁-a = sym p

        map₁-b : transport (λ i → h (map₁-a i) .fst) (snd (fst (fib←h (fib→h ((y₀ , u) , p))))) ≡ u
        map₁-b =
            transport (λ i → h (map₁-a i) .fst) (snd (fst (fib←h (fib→h ((y₀ , u) , p)))))
          ≡⟨⟩
            transp (λ i → h (sym p i) .fst) i0 (transp (λ i → h (p i) .fst) i0 u)
          ≡⟨ subst-sym {A} {λ x → h x .fst} p _ ⟩
            u ∎

      map₂ : transport (λ i → fst (map₁ i) ≡ y) (snd (fib←h (fib→h ((y₀ , u) , p)))) ≡ p
      map₂ =
          transport (λ i → fst (map₁ i) ≡ y) (snd (fib←h (fib→h ((y₀ , u) , p))))
        ≡⟨⟩
          transport (λ i → fst (map₁ i) ≡ y) refl
        ≡⟨⟩
          transport (λ i → p (~ i) ≡ y) refl
        ≡⟨ J (λ y₁ q → transport (λ i → q (~ i) ≡ y₁) refl ≡ q) (JRefl (λ a _ → a) refl) p ⟩
          p ∎

      fib≅h-retract-refl : (u : h y .fst) → fib←h (fib→h ((y , u), refl)) ≡ ((y , u), refl)
      fib≅h-retract-refl u =
          fib←h (fib→h ((y , u), refl))
        ≡⟨⟩
          fib←h (subst (λ x → h x .fst) refl u)
        ≡⟨ cong fib←h (JRefl (λ a _ → a) u) ⟩
          fib←h u
        ≡⟨⟩
          ((y , u), refl) ∎

    fib≅h-section : section fib→h fib←h
    fib≅h-section x =
        fib→h (fib←h x)
      ≡⟨⟩
        subst (λ z → h z .fst) refl x
      ≡⟨ JRefl (λ x' _ → x') x ⟩
        x ∎


  fib≡h : {h : A → Set} (y : A) → fib {Σ A (λ x → h x .fst)} {A} fst y ≡ h y .fst
  fib≡h {h} y = isoToPath (fib≅h {h} y)

  isSet-fib : {h : A → Set} (y : A) → isSet (fib fst y)
  isSet-fib {h} y = subst isSet (sym (fib≡h {h} y)) (h y .snd)

  Covering₀A←A→Set : (A → Set) → (Covering₀ A)
  Covering₀A←A→Set h = record { B = Σ A (λ x → h x .fst) ; f = fst ; p = isSet-fib {h} }


  Covering₀A≅A→Set-section : section Covering₀A→A→Set Covering₀A←A→Set
  Covering₀A≅A→Set-section h = funExt section-x where

    section-x : (x : A) → Covering₀A→A→Set (Covering₀A←A→Set h) x ≡ h x
    section-x x =
        Covering₀A→A→Set (Covering₀A←A→Set h) x
      ≡⟨⟩
        fib fst x , isSet-fib {h} x
      ≡⟨ ΣPathTransport→PathΣ _ (h x) (fib≡h {h} x , lemma) ⟩
        h x ∎ where

      lemma : subst isSet (fib≡h {h} x) (isSet-fib {h} x) ≡ snd (h x)
      lemma = {!!}

  Covering₀A≅A→Set-retract : retract Covering₀A→A→Set Covering₀A←A→Set
  Covering₀A≅A→Set-retract = retract∘≅ Covering₀A→A→Set Covering₀A←A→Set (invIso  Σ≅Covering₀ ) retract-lemma where

    retract-lemma : retract (Covering₀A→A→Set ∘ _≅_.fun Σ≅Covering₀) (_≅_.inv Σ≅Covering₀ ∘ Covering₀A←A→Set)
    retract-lemma (B , f , p) = ΣPathTransport→PathΣ _ _ (map₁ , ΣPathTransport→PathΣ _ _ ({!!} , {!!})) where

      map₁ : Σ A (λ x → Σ B (λ x₁ → f x₁ ≡ x)) ≡ B
      map₁ = isoToPath (iso map₁-fun map₁-inv map₁-section map₁-retract) where

        map₁-fun : Σ A (λ x → Σ B (λ x₁ → f x₁ ≡ x)) → B
        map₁-fun (a , b , r) = b

        map₁-inv : B → Σ A (λ x → Σ B (λ x₁ → f x₁ ≡ x))
        map₁-inv b = f b , b , refl

        map₁-section : section map₁-fun map₁-inv
        map₁-section x = refl

        map₁-retract : retract map₁-fun map₁-inv
        map₁-retract (a , b , r) = ΣPathTransport→PathΣ _ _ (r , ΣPathTransport→PathΣ _ _ (map₁-lemma₁ , {!!})) where

          map₁-lemma₁ : fst (transport (λ i → Σ B (λ x₁ → f x₁ ≡ r i)) (map₁-fun (a , b , r) , (λ _ → f (map₁-fun (a , b , r))))) ≡ b
          map₁-lemma₁ =
              fst (transport (λ i → Σ B (λ x₁ → f x₁ ≡ r i)) (map₁-fun (a , b , r) , (λ _ → f (map₁-fun (a , b , r)))))
            ≡⟨⟩
              transp (λ _ → B) i0 b
            ≡⟨ JRefl (λ a _ → a) b ⟩
              b ∎




          map₁-lemma₂ : subst (λ x → f x ≡ a) map₁-lemma₁ (transp (λ i → f (transp (λ _ → B) (~ i) b) ≡ r i) i0 refl) ≡ r
          map₁-lemma₂ = J (λ a' r' → subst (λ x → f x ≡ a') map₁-lemma₁ (transp (λ i → f (transp (λ _ → B) (~ i) b) ≡ r' i) i0 refl) ≡ r') (
                subst (λ x → f x ≡ f (transp (λ _ → B) (~ i0) b)) map₁-lemma₁ (transp (λ i → f (transp (λ _ → B) (~ i) b) ≡ refl {x = f b} i) i0 refl)
              ≡⟨ cong (subst (λ x → f x ≡ f (transp (λ _ → B) (~ i0) b)) map₁-lemma₁) {!!} ⟩
                subst (λ x → f x ≡ f (transp (λ _ → B) (~ i0) b)) map₁-lemma₁ {!!}
              ≡⟨ {!!} ⟩
                refl ∎
            ) r where

            mini-lemma : transp (λ i → f (transp (λ _ → B) (~ i) b) ≡ refl {x = f b} i) i0 refl ≡ {!!}
            mini-lemma = {!!}

{-
          map₁-lemma₂ : subst (λ x → f x ≡ a) map₁-lemma₁ (snd (subst (fib f) r (b , refl))) ≡ r
          map₁-lemma₂ = J (λ a' r' → subst (λ x → f x ≡ a') map₁-lemma₁ (snd (subst (fib f) r' (b , refl))) ≡ r') (
                subst (λ x → f x ≡ f b) map₁-lemma₁ (snd (subst (fib f) refl (b , refl)))
              ≡⟨ cong ((λ x → f x ≡ f b) map₁-lemma₁) (cong snd (JRefl (λ y → y) refl)) ⟩
                subst (λ x → f x ≡ f b) map₁-lemma₁ (snd {A = B} (b , refl))
              ≡⟨ JRefl {!!} {!!} ⟩
                refl ∎
            ) r
-}
