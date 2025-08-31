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
open import Base
open import Pullback
open import Paths
import UniversalCovering

module SubgroupToCovering (A∙ BG∙ : Pointed ℓ-zero) (hyp-conA : isConnected' ⟨ A∙ ⟩ )
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
