open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Functions.Fibration

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
