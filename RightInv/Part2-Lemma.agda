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

module RightInv.Part2-Lemma (A : Pointed ℓ-zero) (conA : isConnected' ⟨ A ⟩) ((((X , x') , p) , p⋆ , hypCon , fib-set) : PCCovering₀' A) where
  open import RightInv.Base A conA (((X , x') , p) , p⋆ , hypCon , fib-set)

  lemma : (x : X) → e∘e' (e x) ≡ refl {x = e (e' (e x))}
  lemma x = step₁ ∙ step₂ ∙ step₃ ∙ step₄ ∙ step₅ ∙ step₆ ∙ step₇ ∙ step₈ ∙ step₉ ∙ step₁₀
    where
    open import RightInv.Part2-Lemma.Base A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step1 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step2 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step3 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step4 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step5 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step6 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step7 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step8 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step9 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
    open import RightInv.Part2-Lemma.Step10 A conA (((X , x') , p) , p⋆ , hypCon , fib-set) x
