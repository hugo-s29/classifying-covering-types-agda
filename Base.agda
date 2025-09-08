open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation

pick : {W : Type} (a : W) → ⊤ → W
pick x tt = x

isConnected' : (A : Type) → Type
isConnected' A = ∥ A ∥₁ × ((x y : A) → ∥ x ≡ y ∥₁)

record Covering (A : Pointed ℓ-zero) : Type₁ where
  constructor covering
  field
    B : Pointed ℓ-zero
    f : ⟨ B ⟩ → ⟨ A ⟩
    pt⋆ : f (pt B) ≡ pt A
    isCov : (a : ⟨ A ⟩) → isSet (fiber f a)
    isCon : isConnected' ⟨ B ⟩

record SubGroupπ₁ (A : Pointed ℓ-zero) : Type₁ where
  constructor subgroup
  field
    BG : Pointed ℓ-zero
    Bi : ⟨ BG ⟩ → ∥ ⟨ A ⟩ ∥ 3
    Bi⋆ : Bi (pt BG) ≡ ∣ pt A ∣
    isBi : (u : ∥ ⟨ A ⟩ ∥ 3) → isSet (fiber Bi u)
    isCon : isConnected' ⟨ BG ⟩
    isGrp : isGroupoid ⟨ BG ⟩
