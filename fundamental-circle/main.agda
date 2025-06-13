open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1 using (S¹ ; base ; loop)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Int using (ℤ ; _+_)
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

{- PART I. Prove ℤ is a set -}

codeℕ : ℕ → ℕ → Type
codeℕ zero zero = ⊤
codeℕ zero (suc m) = ⊥
codeℕ (suc n) zero = ⊥
codeℕ (suc n) (suc m) = codeℕ n m

codeℕ-refl : (n : ℕ) → codeℕ n n
codeℕ-refl zero = tt
codeℕ-refl (suc n) = codeℕ-refl n

encodeℕ : (m n : ℕ) → (m ≡ n) → codeℕ m n
encodeℕ m n h = subst (codeℕ m) h (codeℕ-refl m)

decodeℕ : (m n : ℕ) → (codeℕ m n) → (m ≡ n)
decodeℕ zero zero h = refl
decodeℕ (suc m) (suc n) h = cong suc (decodeℕ m n h)

codeℕ≅ : (n m : ℕ) → (n ≡ m) ≅ (codeℕ n m)
codeℕ≅ n m = iso (encodeℕ n m) (decodeℕ n m) (s n m) (r n m) where

  s : (n m : ℕ) → section (encodeℕ n m) (decodeℕ n m)
  s zero zero _ = refl
  s (suc n) (suc m) p = s n m p

  r : (n m : ℕ) → retract (encodeℕ n m) (decodeℕ n m)
  r n m p = J (λ k q → decodeℕ n k (encodeℕ n k q) ≡ q) (codeℕ-refl≡refl n) p where

    codeℕ-refl≡refl : (n : ℕ) → decodeℕ n n (encodeℕ n n refl) ≡ refl
    codeℕ-refl≡refl zero = refl
    codeℕ-refl≡refl (suc n) i = cong suc (codeℕ-refl≡refl n i)

codeℕ≡ : (n m : ℕ) → (n ≡ m) ≡ (codeℕ n m)
codeℕ≡ n m = isoToPath (codeℕ≅ n m)

isProp⊤ : isProp ⊤
isProp⊤ tt tt = refl

codeℕ-isProp : (n m : ℕ) → isProp (codeℕ n m)
codeℕ-isProp zero zero = isProp⊤
codeℕ-isProp zero (suc m) = λ ()
codeℕ-isProp (suc n) zero = λ ()
codeℕ-isProp (suc n) (suc m) = codeℕ-isProp n m

isSetℕ : isSet ℕ
isSetℕ n m = subst isProp (sym (codeℕ≡ n m)) (codeℕ-isProp n m)

code⊎ : {A B : Type} → A ⊎ B → A ⊎ B → Type
code⊎ (inl x) (inl y) = x ≡ y
code⊎ (inl x) (inr y) = ⊥
code⊎ (inr x) (inl y) = ⊥
code⊎ (inr x) (inr y) = x ≡ y

code⊎-refl : {A B : Type} (x : A ⊎ B) → code⊎ x x
code⊎-refl (inl x) = refl
code⊎-refl (inr x) = refl

encode⊎ : {A B : Type} (x y : A ⊎ B) → x ≡ y → code⊎ x y
encode⊎ x y h = subst (code⊎ x) h (code⊎-refl x)

encode⊎-refl : {A B : Type} (x : A ⊎ B) → encode⊎ x x refl ≡ code⊎-refl x
encode⊎-refl x = JRefl (λ y p → code⊎ x y) (code⊎-refl x)

decode⊎ : {A B : Type} (x y : A ⊎ B) → code⊎ x y → x ≡ y
decode⊎ (inl x) (inl x₁) h = cong inl h
decode⊎ (inr x) (inr x₁) h = cong inr h

decode⊎-refl : {A B : Type} (x : A ⊎ B) → decode⊎ x x (code⊎-refl x) ≡ refl
decode⊎-refl (inl x) = refl
decode⊎-refl (inr x) = refl

code⊎≅ : {A B : Type} (x y : A ⊎ B) → (x ≡ y) ≅ (code⊎ x y)
code⊎≅ x y = iso (encode⊎ x y) (decode⊎ x y) (s x y) (r x y) where

    s : {A B : Type} (x y : A ⊎ B) → section (encode⊎ x y) (decode⊎ x y)
    s {A} {B} (inl x) (inl _) p = J (λ y' p' → encode⊎ {A} {B} (inl x) (inl y') (cong inl p') ≡ p') (encode⊎-refl {A} {B} (inl x)) p
    s {A} {B} (inr x) (inr _) p = J (λ y' p' → encode⊎ {A} {B} (inr x) (inr y') (cong inr p') ≡ p') (encode⊎-refl {A} {B} (inr x)) p

    r : {A B : Type} (x y : A ⊎ B) → retract (encode⊎ x y) (decode⊎ x y)
    r x y p = J (λ y' p' → decode⊎ x y' (encode⊎ x y' p') ≡ p') (code⊎-refl≡refl x) p where

      code⊎-refl≡refl : {A B : Type} (x : A ⊎ B) → decode⊎ x x (encode⊎ x x refl) ≡ refl
      code⊎-refl≡refl x =
        decode⊎ x x (encode⊎ x x refl)
        ≡⟨ cong (decode⊎ x x) (encode⊎-refl x) ⟩
        decode⊎ x x (code⊎-refl x)
        ≡⟨ decode⊎-refl x ⟩
        refl

code⊎≡ : {A B : Type} (x y : A ⊎ B) → (x ≡ y) ≡ (code⊎ x y)
code⊎≡ x y = isoToPath (code⊎≅ x y)


ℤ≡ℕ⊎ℕ : ℤ ≡ ℕ ⊎ ℕ
ℤ≡ℕ⊎ℕ = isoToPath (iso ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ ℤ≡ℕ⊎ℕ-section ℤ≡ℕ⊎ℕ-retract) where

  ℤ→ℕ⊎ℕ : ℤ → ℕ ⊎ ℕ
  ℤ→ℕ⊎ℕ (ℤ.pos n) = inl n
  ℤ→ℕ⊎ℕ (ℤ.negsuc n) = inr n

  ℕ⊎ℕ→ℤ : ℕ ⊎ ℕ → ℤ
  ℕ⊎ℕ→ℤ (inl n) = ℤ.pos n
  ℕ⊎ℕ→ℤ (inr n) = ℤ.negsuc n

  ℤ≡ℕ⊎ℕ-section : section ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
  ℤ≡ℕ⊎ℕ-section (inl x) = refl
  ℤ≡ℕ⊎ℕ-section (inr x) = refl

  ℤ≡ℕ⊎ℕ-retract : retract ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
  ℤ≡ℕ⊎ℕ-retract (ℤ.pos n) = refl
  ℤ≡ℕ⊎ℕ-retract (ℤ.negsuc n) = refl

code⊎-isProp : {A B : Type} → isSet A → isSet B → (x y : A ⊎ B) → isProp (code⊎ x y)
code⊎-isProp hA hB (inl x) (inl y) = hA x y
code⊎-isProp hA hB (inl x) (inr y) = λ ()
code⊎-isProp hA hB (inr x) (inl y) = λ ()
code⊎-isProp hA hB (inr x) (inr y) = hB x y

isSet⊎ : {A B : Type} → isSet A → isSet B → isSet (A ⊎ B)
isSet⊎ hA hB = λ x y → subst isProp (sym (code⊎≡ x y)) (code⊎-isProp hA hB x y)


isSetℤ : isSet ℤ
isSetℤ = subst isSet (sym ℤ≡ℕ⊎ℕ) (isSet⊎ isSetℕ isSetℕ)


{- Part II. Prove ℤ = π₁(S¹) -}

Ω : (A : Type) (a : A) → Type
Ω A a = a ≡ a

ΩS¹ : Type
ΩS¹ = Ω S¹ base

loop⁻¹ : ΩS¹
loop⁻¹ = sym loop

loop_times : ℤ → Ω S¹ base
loop ℤ.pos zero times = refl
loop ℤ.pos (suc n) times = loop (ℤ.pos n) times ∙ loop
loop ℤ.negsuc zero times = loop⁻¹
loop ℤ.negsuc (suc n) times = loop (ℤ.negsuc n) times ∙ loop⁻¹

sucℤ : ℤ → ℤ
sucℤ (ℤ.pos n) = ℤ.pos (suc n)
sucℤ (ℤ.negsuc zero) = ℤ.pos zero
sucℤ (ℤ.negsuc (suc n)) = ℤ.negsuc n

predℤ : ℤ → ℤ
predℤ (ℤ.pos zero) = ℤ.negsuc zero
predℤ (ℤ.pos (suc n)) = ℤ.pos n
predℤ (ℤ.negsuc n) = ℤ.negsuc (suc n)

suc∘predℤ : section sucℤ predℤ
suc∘predℤ (ℤ.pos zero) = refl
suc∘predℤ (ℤ.pos (suc n)) = refl
suc∘predℤ (ℤ.negsuc zero) = refl
suc∘predℤ (ℤ.negsuc (suc n)) = refl

pred∘sucℤ : retract sucℤ predℤ
pred∘sucℤ (ℤ.pos zero) = refl
pred∘sucℤ (ℤ.pos (suc n)) = refl
pred∘sucℤ (ℤ.negsuc zero) = refl
pred∘sucℤ (ℤ.negsuc (suc n)) = refl

sucℤ≡ : ℤ ≡ ℤ
sucℤ≡ = isoToPath (iso sucℤ predℤ suc∘predℤ pred∘sucℤ)

predℤ≡ : ℤ ≡ ℤ
predℤ≡ = sym sucℤ≡

helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucℤ≡ i

wind : (x : S¹) → base ≡ x → helix x
wind _ p = subst helix p (ℤ.pos zero)

path-over : {A : Type} {x y : A} (B : A → Type) (p : x ≡ y) (u : B x) (v : B y) → Type
path-over B p u v = subst B p u ≡ v

syntax path-over B p u v = u ≡ v [ B ↓ p ]

PathD : {A0 A1 : Type} (p : A0 ≡ A1) (x : A0) (y : A1) → Type
PathD p x y = transport p x ≡ y

S¹-ind : {B : S¹ → Type} → (b : B base) → PathP (λ i → B (loop i)) b b → (x : S¹) → B x
S¹-ind b p base = b
S¹-ind b p (loop i) = p i

PathD→PathP : {A : I → Type} (x : A i0) (y : A i1) → (PathD (λ i → A i) x y) → (PathP A x y)
PathD→PathP {A} x y = _≅_.inv (PathPIsoPath A x y)

S¹-ind' : {B : S¹ → Type} → (b : B base) → PathD (λ i → B (loop i)) b b  → (x : S¹) → B x
S¹-ind' b p = S¹-ind b (PathD→PathP b b p)

transport-path-fibration : {A : Type} {x y z : A} (q : x ≡ y) (p : y ≡ z) → transport (λ i → x ≡ p i) q ≡ q ∙ p
transport-path-fibration  {_} {x} q = J (λ _ p → transport (λ i → x ≡ p i) q ≡ q ∙ p)
  (
    transport refl q
  ≡⟨ JRefl (λ a _ → a) q ⟩
    q
  ≡⟨ rUnit q ⟩
    q ∙ refl ∎
  )

loops∙loop-suc : (n : ℤ) → loop n times ∙ loop ≡ loop sucℤ n times
loops∙loop-suc (ℤ.pos n) = refl
loops∙loop-suc (ℤ.negsuc zero) = lCancel loop
loops∙loop-suc (ℤ.negsuc (suc n)) =
    (loop ℤ.negsuc n times ∙ loop⁻¹) ∙ loop
  ≡⟨ sym (assoc _ _ _) ⟩
    loop ℤ.negsuc n times ∙ (loop⁻¹ ∙ loop)
  ≡⟨ cong (λ p → loop (ℤ.negsuc n) times ∙ p) (lCancel _) ⟩
    loop (ℤ.negsuc n) times ∙ refl
  ≡⟨ sym (rUnit _) ⟩
    loop (ℤ.negsuc n) times ∎


unwind : (x : S¹) → helix x → base ≡ x
unwind = S¹-ind' {B = λ x → helix x → base ≡ x} loop_times (
    transport (λ i → sucℤ≡ i → base ≡ loop i) loop_times
  ≡⟨ refl ⟩
    (λ n → transport (λ i → base ≡ loop i) (loop (transport predℤ≡ n) times))
  ≡⟨ refl ⟩
    (λ n → transport (λ i → base ≡ loop i) (loop (predℤ n) times))
  ≡⟨ funExt (λ n →
      loop predℤ n times ∙ loop
    ≡⟨ loops∙loop-suc (predℤ n) ⟩
      loop (sucℤ (predℤ n)) times
    ≡⟨ cong loop_times (suc∘predℤ n) ⟩
      loop n times ∎
  )⟩
    loop_times ∎
  )

ΩS¹≡ℤ : ΩS¹ ≡ ℤ
ΩS¹≡ℤ = isoToPath (iso (wind base) (unwind base) s (r base)) where

  s : section (wind base) (unwind base)
  s (ℤ.pos zero) = refl
  s (ℤ.pos (suc n)) = cong sucℤ (s (ℤ.pos n))
  s (ℤ.negsuc zero) = refl
  s (ℤ.negsuc (suc n)) = cong predℤ (s (ℤ.negsuc n))

  r : (x : S¹) → retract (wind x) (unwind x)
  r x p = J (λ x' p' → unwind x' (wind x' p') ≡ p') refl p
