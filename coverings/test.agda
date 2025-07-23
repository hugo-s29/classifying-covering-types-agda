open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
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
open import Paths


private
  {- Taken from Cubical library -}
  module Test (A B : Type) (f : A → B) (g : B → A) (s : section f g) (t : retract f g) (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
    fill0 : I → I → A
    fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                              ; (i = i0) → g y })
                    (inS (g (p0 (~ i))))

    fill1 : I → I → A
    fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                              ; (i = i0) → g y })
                    (inS (g (p1 (~ i))))

    fill2 : I → I → A
    fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                              ; (i = i0) → fill0 k i1 })
                    (inS (g y))

    p : x0 ≡ x1
    p i = fill2 i i1


module _ {A B : Type} (f : A → B) (g : B → A) (rinv : section f g) (linv : retract f g) (h : (b : B) → cong g (rinv b) ≡ linv (g b)) where

  biinv : BiInvEquiv A B
  biinv .BiInvEquiv.fun = f
  biinv .BiInvEquiv.invr = g
  biinv .BiInvEquiv.invr-rightInv = rinv
  biinv .BiInvEquiv.invl = g
  biinv .BiInvEquiv.invl-leftInv = linv

  A≃B : A ≃ B
  A≃B = biInvEquiv→Equiv-left biinv

  A≡B : A ≡ B
  A≡B = ua A≃B

  trA≡B : (a : A) → transport A≡B a ≡ f a
  trA≡B a = uaβ A≃B a

  trA≡B⁻ : (b : B) → transport⁻ A≡B b ≡ g b
  trA≡B⁻ b = ~uaβ A≃B b

  lemma : (b : B) → (transport refl b ≡ transport refl b ) ≡ (transport (ua (idEquiv B)) b ≡ transport (ua (idEquiv B)) b)
  lemma b = refl

  lemma' : (b : B) → transport⁻ refl b ≡ transport⁻ (ua (idEquiv B)) b
  lemma' b = refl

  retEq≡inv : (a : A) → retEq A≃B a ≡ linv a
  retEq≡inv a = p≡linv
      where

      rinv' : (b : B) → f (g b) ≡ b
      rinv' = BiInvEquiv.invl-rightInv biinv

      open Test A B f g rinv' linv (f a) (g (f a)) a (rinv' (f a)) refl

      top-fill1 : (λ i → fill1 i i1) ≡ linv a
      top-fill1 = lUnit (linv a) ⁻¹

{-
  invr≡invl : ∀ b → invr b ≡ invl b
  invr≡invl b =            invr b   ≡⟨ sym (invl-leftInv (invr b)) ⟩
                invl (fun (invr b)) ≡⟨ cong invl (invr-rightInv b) ⟩
                invl b              ∎ -}

      rinv'≡rinv : rinv' ≡ rinv
      rinv'≡rinv = funExt(λ b →
          cong f (linv (g b) ⁻¹ ∙ cong g (rinv b) ∙ refl) ⁻¹ ∙ rinv b
        ≡⟨ cong (λ u → cong f (linv (g b) ⁻¹ ∙ u) ⁻¹ ∙ rinv b) (rUnit _ ⁻¹) ⟩
          cong f (linv (g b) ⁻¹ ∙ cong g (rinv b)) ⁻¹ ∙ rinv b
        ≡⟨ cong (λ u → cong f (linv (g b) ⁻¹ ∙ u) ⁻¹ ∙ rinv b) (h b) ⟩
          cong f (linv (g b) ⁻¹ ∙ linv (g b)) ⁻¹ ∙ rinv b
        ≡⟨ cong (λ u → cong f u ⁻¹ ∙ rinv b) (lCancel (linv (g b))) ⟩
          cong f refl ⁻¹ ∙ rinv b
        ≡⟨ lUnit _ ⁻¹ ⟩
          rinv b ∎)

      h' : (b : B) → cong g (rinv' b) ≡ linv (g b)
      h' b = subst⁻ (λ u → cong g (u b) ≡ linv (g b)) rinv'≡rinv (h b)

      top-fill0 : (λ i → fill0 i i1) ≡ refl
      top-fill0 =
        cong g (rinv' (f a)) ⁻¹ ∙ linv (g (f a))
        ≡⟨ cong (cong g (rinv' (f a)) ⁻¹ ∙_) (h' (f a)) ⁻¹ ⟩
        cong g (rinv' (f a)) ⁻¹ ∙ cong g (rinv' (f a))
        ≡⟨ lCancel _ ⟩
        refl ∎

      p≡linv : p ≡ linv a
      p≡linv =
          p
        ≡⟨ {!!} ⟩
          ((λ i → fill0 i i1) ∙∙ refl ∙∙ (λ i → fill1 i i1))
        ≡⟨ cong₂ (λ u v → _∙∙_∙∙_ {w = a} u refl v) top-fill0 top-fill1 ⟩
          (refl ∙∙ refl ∙∙ linv a)
        ≡⟨ lUnit _ ⁻¹ ⟩
          linv a ∎


  testing : (i : I) → B ≡ ua (idEquiv B) i
  testing i j = uaIdEquiv {A = B} i (i ∧ j)

  testing' : (i : I) → refl {x = B} ≡ uaIdEquiv {A = B} i
  testing' i j k = uaIdEquiv {A = B} i (j ∧ k ∧ ~ k)

  lem' : (b : B) → PathP (λ i → transport⁻ (uaIdEquiv i) (transport (uaIdEquiv i) b) ≡ b) (transport⁻Transport (ua (idEquiv B)) b) (transport⁻Transport refl b)
  lem' b = cong (λ x → transport⁻Transport x b) uaIdEquiv

  lem'' : (b : B) → (λ (i : I) → transport⁻ (uaIdEquiv i) (transport (uaIdEquiv i) b) ≡ b) ≡ (λ _ → transport⁻ refl (transport refl b) ≡ b)
  lem'' b j i = transport⁻ (λ k → uaIdEquiv {A = B} (i ∨ j) k) (transport (uaIdEquiv (i ∨ j)) b) ≡ b

  test₀ : (b : B) → transport⁻ (ua (idEquiv B)) (transport (ua (idEquiv B)) b) ≡ transport⁻ refl (transport refl b)
  test₀ b = refl

  lem : (b : B) → transport⁻Transport (ua (idEquiv B)) b ≡ transport⁻Transport refl b
  lem b i = transport⁻Transport {B = B} {!!} b

  {-
  lem : (b : B) → PathP (λ i → transport⁻ (λ _ → B) (transport (λ _ → B) b) ≡ b) (transport⁻Transport (ua (idEquiv B)) b) (transport⁻Transport refl b)
  lem b = {!!}
  -}

  test : (a : A) → PathP (λ i → transport⁻ (ua A≃B) (transport (ua A≃B) a) ≡ invEq A≃B (f a)) (congP (λ i b → ~uaβ A≃B b i) (uaβ A≃B a)) (transport⁻Transport (ua A≃B) a ∙ retEq A≃B a ⁻¹)
  test = {!!}
    {-
  EquivJ (λ A A≃B → (a : A) → congP (λ i b → ~uaβ A≃B b i) (uaβ A≃B a) ≡ transport⁻Transport (ua A≃B) a ∙ retEq A≃B a ⁻¹) (λ b →
    let z = cong {x = refl} {y = ua (idEquiv B)} (λ u → transport⁻Transport u b) {!!}  in
        {-
j = i0 ⊢ B
j = i1 ⊢ B
i = i0 ⊢ B
i = i1 ⊢ ua (idEquiv B) j
        -}
        congP (λ i x → transportRefl x i) (transportRefl b)
      ≡⟨⟩
        transport⁻Transport refl b
      ≡⟨ cong {x = refl} {y = ua (idEquiv B)} (λ u → transport⁻Transport u b) {!lem !} ⟩
        -- congP (λ i u → transport⁻Transport {A = B} {B = B} u b i) uaIdEquiv
        transport⁻Transport (ua (idEquiv B)) b
      ≡⟨ rUnit _ ⟩
        transport⁻Transport (ua (idEquiv B)) b ∙ refl ∎
    ) A≃B

  {-
  test : (a : A) → congP (λ i b → ~uaβ A≃B b i) (uaβ A≃B a) ≡ transport⁻Transport A≡B a ∙ linv a ⁻¹
  test = EquivJ (λ A A≃B → (a : A) → congP (λ i b → ~uaβ A≃B b i) (uaβ A≃B a) ≡ {!!}) {!!} {!!}
  -}
-}
