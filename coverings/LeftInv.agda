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
open import UniversalCovering

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

  ∥p∥ : ∥ pullbackΣ Bi ∣_∣ ∥ 3 → ∥ ⟨ A ⟩ ∥ 3
  ∥p∥ = ∥-∥ₕ-map (λ x → x .snd .fst)

  Bi∘s≡∥p∥ : Bi ∘ s ≡ ∥p∥
  Bi∘s≡∥p∥ = funExt (∥-∥ₕ-elim {B = λ x → Bi (s x) ≡ ∥p∥ x} (λ x → isOfHLevelTruncPath {y = ∥p∥ x}) (λ (_ , _ , q) → q))

  Bi∘tr≡Bi∘s : (x : ∥ pullbackΣ Bi ∣_∣ ∥ 3) → transport refl (Bi (transport⁻ ⟨BG⟩≡∥X∥ x)) ≡ Bi (s x)
  Bi∘tr≡Bi∘s x = transportRefl _ ∙ cong Bi (transportIsoToPath⁻ ⟨BG⟩≅∥X∥ x)

  Bi≡Bi∘s : PathP (λ i → ⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3) Bi (Bi ∘ s)
  Bi≡Bi∘s = subst (PathP (λ i → ⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3) Bi) (funExt Bi∘tr≡Bi∘s) (funTypeTransp (λ X → X) (λ _ → ∥ ⟨ A ⟩ ∥ 3) ⟨BG⟩≡∥X∥ Bi) where

  Bi≡∥p∥∙ : PathP (λ i → (⟨BG⟩≡∥X∥ ∙ refl) i → ∥ ⟨ A ⟩ ∥ 3) Bi ∥p∥
  Bi≡∥p∥∙ = compPathP' {A = Type} {B = λ X → X → ∥ ⟨ A ⟩ ∥ 3}
    {x' = Bi}
    {y' = Bi ∘ s}
    {z' = ∥p∥}
    {p = ⟨BG⟩≡∥X∥}
    {q = refl}
    Bi≡Bi∘s
    Bi∘s≡∥p∥


  Bi≡∥p∥ : PathP (λ i → ⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3) Bi ∥p∥
  Bi≡∥p∥ = subst (λ r → PathP (λ i → r i → ∥ ⟨ A ⟩ ∥ 3) Bi ∥p∥) (rUnit ⟨BG⟩≡∥X∥ ⁻¹) Bi≡∥p∥∙

  ∣x∣ : ∥ pullbackΣ Bi ∣_∣ ∥ 3
  ∣x∣ = ∣ pt BG , pt A , Bi-⋆ ∣

  ∣x∣' : ∥ pullbackΣ Bi ∣_∣ ∥ 3
  ∣x∣' = ∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) (Bi (pt BG)) refl

  ptBG≡∣x∣' : PathP (λ i → ⟨BG⟩≡∥X∥ i) (pt BG) ∣x∣'
  ptBG≡∣x∣' = toPathP (transportRefl ∣x∣')


  ∣x∣'≡∣x∣ : ∣x∣' ≡ ∣x∣
  ∣x∣'≡∣x∣ = cong₂ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣)) Bi-⋆ (toPathP ( substInPathsL Bi-⋆ refl ∙ lUnit _ ⁻¹))

  ptBG≡∣x∣∙ : PathP (λ i → (⟨BG⟩≡∥X∥ ∙ refl) i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣
  ptBG≡∣x∣∙ = compPathP' {A = Type} {B = λ X → X}
    {x' = pt BG}
    {y' = ∣x∣'}
    {z' = ∣x∣}
    {p = ⟨BG⟩≡∥X∥} {q = refl}
    ptBG≡∣x∣'
    ∣x∣'≡∣x∣

  ptBG≡∣x∣ : PathP (λ i → ⟨BG⟩≡∥X∥ i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣
  ptBG≡∣x∣ = subst (λ r → PathP (λ i → r i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣) (rUnit ⟨BG⟩≡∥X∥ ⁻¹) ptBG≡∣x∣∙

  congP1 : congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣' ≡ cong Bi (s∘t (pt BG)) ⁻¹
  congP1 =
      congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣'
    ≡⟨ {!!} ⟩
      {!!}
    ≡⟨ {!!} ⟩
      {!!}
    ≡⟨ {!!} ⟩
      cong Bi (s∘t (pt BG)) ⁻¹ ∎

  congP2 : congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣ ≡ cong Bi (s∘t (pt BG) ) ∙ Bi-⋆
  congP2 =
      congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣
    ≡⟨ cong (congP (λ i → Bi∘s≡∥p∥ i)) ? ⟩
      congP (λ i → Bi∘s≡∥p∥ i) {!!}
    ≡⟨ {!!} ⟩
      {!!}
    ≡⟨ {!!} ⟩
      cong Bi (s∘t (pt BG) ) ∙ Bi-⋆ ∎

  Bi⋆≡path : congP (λ i → Bi≡∥p∥∙ i) ptBG≡∣x∣∙ ≡ Bi-⋆
  Bi⋆≡path =
      congP (λ i → Bi≡∥p∥∙ i) ptBG≡∣x∣∙
    ≡⟨ {!!} ⟩ -- congP-compPathP' {B = λ X → X} _ _ ⟨BG⟩≡∥X∥ (pt BG) ∣x∣' ptBG≡∣x∣' _ refl ∣x∣ ∣x∣'≡∣x∣ Bi (Bi ∘ s) ∥p∥ Bi≡Bi∘s Bi∘s≡∥p∥ ⟩ -- attention, c'est lent, très lent
      compPathP' {A = Type} {p = ⟨BG⟩≡∥X∥} {q = refl} (congP (λ i → Bi≡Bi∘s i) ptBG≡∣x∣') (congP (λ i → Bi∘s≡∥p∥ i) ∣x∣'≡∣x∣)
    ≡⟨ cong₂ (compPathP' {A = Type} {p = ⟨BG⟩≡∥X∥} {q = refl}) congP1 congP2 ⟩
      compPathP' {A = Type} {p = ⟨BG⟩≡∥X∥} {q = refl} (cong Bi (s∘t (pt BG)) ⁻¹) (cong Bi (s∘t (pt BG) ) ∙ Bi-⋆)
    ≡⟨ compPathP'-nondep {r = ⟨BG⟩≡∥X∥} {s = refl} (cong Bi (s∘t (pt BG)) ⁻¹) (cong Bi (s∘t (pt BG) ) ∙ Bi-⋆) ⟩
      (cong Bi (s∘t (pt BG)) ⁻¹) ∙ (cong Bi (s∘t (pt BG) ) ∙ Bi-⋆)
    ≡⟨ assoc _ _ _ ⟩
      ((cong Bi (s∘t (pt BG)) ⁻¹) ∙ cong Bi (s∘t (pt BG) )) ∙ Bi-⋆
    ≡⟨ cong (_∙ Bi-⋆) (lCancel _) ∙ lUnit Bi-⋆ ⁻¹ ⟩
      Bi-⋆ ∎


  {-
  ptBG≡∣x∣ : PathP (λ i → ⟨BG⟩≡∥X∥ i) (pt BG) ∣ pt BG , pt A , Bi-⋆ ∣
  ptBG≡∣x∣ = toPathP (
      transport ⟨BG⟩≡∥X∥ (pt BG)
    ≡⟨ transportIsoToPath ⟨BG⟩≅∥X∥ (pt BG) ⟩
      ∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) (Bi (pt BG)) refl
    ≡⟨ cong₂ (∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣)) Bi-⋆ (toPathP ( substInPathsL Bi-⋆ refl ∙ lUnit _ ⁻¹)) ⟩
      ∥-∥ₕ-elim {B = λ a → Bi (pt BG) ≡ a → ∥ pullbackΣ Bi ∣_∣ ∥ 3} (λ _ → isGroupoidΠ λ _ → isOfHLevelTrunc 3) (λ a r → ∣ pt BG , a , r ∣) ∣ pt A ∣ Bi-⋆
    ≡⟨⟩
      ∣ pt BG , pt A , Bi-⋆ ∣ ∎)


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

  -}
  {-
  lem : PathP (λ i → Σ (⟨BG⟩≡∥X∥ i × (⟨BG⟩≡∥X∥ i → ∥ ⟨ A ⟩ ∥ 3)) λ (x , f) → f x ≡ ∣ pt A ∣) ((pt BG ,  Bi), Bi-⋆ ) ((∣ pt BG , pt A , Bi-⋆ ∣ , ∥p∥), refl)
  lem i = (
    toPathP (transportIsoToPath ⟨BG⟩≅∥X∥ (pt BG)) i ,
    let u = funTypeTransp (λ X → X) (λ _ → ∥ ⟨ A ⟩ ∥ 3) ⟨BG⟩≡∥X∥ Bi i in
    {!!}
      )
     , {!!}
  -}

  {-
  Bi⋆≡path : congP (λ i → Bi≡∥p∥ i) ptBG≡∣x∣ ≡ Bi-⋆
  Bi⋆≡path = {!!}

  Bi⋆≡refl : transport (λ i → congP (λ i a → Bi≡∥p∥ i a ≡ ∣ pt A ∣) ptBG≡∣x∣ i) Bi-⋆ ≡ refl
  Bi⋆≡refl =
      subst (λ x → x ≡ ∣ pt A ∣) (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) Bi-⋆
    ≡⟨ substInPathsR (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) Bi-⋆ ⟩
      (λ i → Bi≡∥p∥ i (ptBG≡∣x∣ i)) ⁻¹ ∙ Bi-⋆
    ≡⟨ cong (λ x → x ⁻¹ ∙ Bi-⋆) Bi⋆≡path ⟩
      Bi-⋆ ⁻¹ ∙ Bi-⋆
    ≡⟨ lCancel Bi-⋆ ⟩
      refl

  {-
  -}

  leftInv : SubGroupπ₁'←PCCovering₀' A conA (SubGroupπ₁'→PCCovering₀' A conA ((BG , Bi) , Bi-⋆ , conBG , grpBG , Bi-fib)) ≡ ((BG , Bi) , Bi-⋆ , conBG , grpBG , Bi-fib)
  leftInv = ΣPathP ((ΣPathP ((ΣPathP (⟨BG⟩≡∥X∥ , ptBG≡∣x∣)) , Bi≡∥p∥)) , ΣPathP ({!!} , toPathP (isProp× isConnected'IsProp (isProp× isPropIsGroupoid (isPropΠ (λ _ → isPropIsSet))) _ _))) ⁻¹

  -}
