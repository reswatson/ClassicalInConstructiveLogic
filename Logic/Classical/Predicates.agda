

{-# OPTIONS --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Logic.Classical.Predicates where

open import Relation.Nullary
open import Data.Empty

open import Logic.Classical.Base renaming (isProp to isProp' ; isProp¬ to isProp¬') hiding (Iso ; section ; retract) 
open import Logic.Classical.Properties hiding (transport)
open import Logic.Conversions
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

private 
  variable
    ℓ ℓ' : Level
private
  variable
    A : Set ℓ
    B : Set ℓ'

----------------------------

-- lemmas for pushing ¬¬ through ∀
¬¬∀-Apply¬¬-dep : {A : Set ℓ} → {B : A → Set ℓ'} →
  ¬¬ ((x : A) → B x) → (x' : A) → ¬¬ (B x')
¬¬∀-Apply¬¬-dep {ℓ}{ℓ'}{A}{B} x y z = x (λ w → z (w y))

¬¬∀-Apply¬¬-dep' : {A : Set ℓ} → {B : A → Set ℓ'} →
  ¬¬ ((x : A) → ¬¬ (B x)) → (x' : A) → ¬¬ (B x')
¬¬∀-Apply¬¬-dep' {ℓ}{ℓ'}{A}{B} x y z = x (λ w → w y z)

¬¬∀→∀¬¬ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'}{f : A → B}{g : B → A} →
  ¬¬ (∀ b → f (g b) ≡ b) → (∀ b → ¬¬ (f (g b) ≡ b))
¬¬∀→∀¬¬ nnA b x = ¬¬∀-Apply¬¬-dep nnA b x

isProp∀ : (f : A -> Set ℓ') → isProp (∀ (a : A) → ISTRUE (f a))
isProp∀ f = λ x y i a x₁ → y a x₁

ISTRUE∀ : (f : A -> Set ℓ') → ISTRUE (∀ (a : A) → ISTRUE (f a)) ≡ (∀ (a : A) → ISTRUE (f a))
ISTRUE∀ {ℓ}{ℓ'}{A} f = isoToPath
  (iso ¬¬∀-Apply¬¬-dep' A→¬¬A (λ b i x' x → b x' x) λ a i x → x (λ x₁ z → a (λ z₁ → z₁ x₁ z))) 

----------------------------

-- Logic.Classical.Base and Logic.Classical.Properties define classical propositional
-- logic by giving a construction of classical operators such as AND and OR in cubical-
-- compatible Agda. This file uses Cubical Agda. This enables us to use Isomorphisms for
-- substitutions more generally, notwithstanding possible level subtetlies. 

-- Here we say that a Type is "outer classical" if it is double-negative invariant.
-- ISTRUE is used as in Logic.Classical.Base and Logic.Classical.Properties to express
-- what is classically 'true', ie the double-negation of constructive 'truth'. There
-- a classical fragment is demonstarted. Outer Classical is more general than that,
-- but terms in both are double-negation invariant.

-- Sometimes, due to the definition of cubical equality, in lieu of level cumulativity,
-- we will need to be careful about Levels, so we have:

Lift-ISTRUE-commutativity : ∀ {A : Set ℓ} →
  (ISTRUE (Lift {i = ℓ}{j = ℓ'} A)) ≡ (Lift {i = ℓ}{j = ℓ'} (ISTRUE A))
Lift-ISTRUE-commutativity {ℓ}{ℓ'}{A} = isoToPath
  (iso (λ z → lift (λ z₁ → z (λ z₂ → z₁ (z₂ .lower))))
       (λ z z₁ → z .lower (λ z₂ → z₁ (lift z₂))) (λ b i → b) (λ a i x → a x))

data OuterClassical (A : Set ℓ) : Set (ℓ-suc ℓ) where
  invariant : ((ISTRUE A) ≡ A) -> OuterClassical A

extract-invariant : OuterClassical A → ISTRUE A ≡ A
extract-invariant (invariant x) = x

-- When a Type is outer classical it is an isProp proposition:
isPropOuterClassical : OuterClassical A → isProp A
isPropOuterClassical {ℓ}{A} (invariant inv) = transport (cong (λ x → isProp x) inv) isp
  where
    isp : isProp (ISTRUE A)
    isp = λ x y i x₁ → y x₁

-- Any type can be 'wrapped' in an ISTRUE to form an OuterClassical variant:
wrapping-lemma : ∀ {A : Set ℓ} → OuterClassical (ISTRUE A)
wrapping-lemma {ℓ}{A} = invariant (isoToPath
  (iso (λ z z₁ → z (λ z₂ → z₂ z₁))
       (λ z z₁ → z₁ z) (λ b i x → b x) (λ a i x → x (λ z → a (λ z₁ → z₁ z)))))

---------------------------------------------
-- Quantifiers - Universal and Existential --
---------------------------------------------

-- We now have that the universal quantifier ∀ is also outer classical when the
-- expression it is quantified over is outer classical:
OuterClassical∀ : {A : Set ℓ} (f : (a : A) → Set ℓ') →
  (∀ (a : A) → OuterClassical (f a)) → OuterClassical (∀ (a : A) → f a)
OuterClassical∀ {ℓ}{ℓ'}{A} f oc = invariant ((sym step2) ∙ step3 ∙ step1)  
  where
    hlp : ∀ (a : A) → (ISTRUE (f a)) ≡ f a
    hlp a = extract-invariant (oc a) 
    step1 : (∀ (a : A) → ISTRUE (f a)) ≡ (∀ (a : A) → f a)
    step1 = cubical≡-∀lemma (λ z → ISTRUE (f z)) f hlp
    step2 : ISTRUE ((a : A) → ISTRUE (f a)) ≡ ISTRUE ((a : A) → f a)
    step2 = cong (λ x → ISTRUE x) step1
    step3 : ISTRUE ((a : A) → ISTRUE (f a)) ≡ (∀ (a : A) → ISTRUE (f a))
    step3 = ISTRUE∀ f

-- We can now do something similar for a 'classical' ∃ quantifier:
∃ : (A : Set ℓ) (B : A → Set ℓ') → Type (ℓ-max ℓ ℓ')
∃ A B = ISTRUE (Σ A B)

isProp∃ :  (A : Set ℓ) (B : A → Set ℓ') → isProp (∃ A B)
isProp∃ A B = λ x y i z → y z

isProp¬∀ : (A : Set ℓ) (B : A → Set ℓ') → isProp (¬ (∀ (a : A) → ¬ (B a)))
isProp¬∀ A B = λ x y i x₁ → x x₁

¬∀¬≡∃Hlp1 : (A : Set ℓ) (B : A → Set ℓ') → (¬ (∀ (a : A) → ¬ (B a))) → ∃ A B
¬∀¬≡∃Hlp1 A B = λ z z₁ → z (λ a z₂ → z₁ (a , z₂))

¬∀¬≡∃Hlp2 : (A : Set ℓ) (B : A → Set ℓ') → ∃ A B → (¬ (∀ (a : A) → ¬ (B a)))
¬∀¬≡∃Hlp2 A B = λ z z₁ → z (λ z₂ → z₁ (z₂ .fst) (z₂ .snd)) 

¬∀¬≡∃ : (A : Set ℓ) (B : A → Set ℓ') → (¬ (∀ (a : A) → ¬ (B a))) ≡ (∃ A B)
¬∀¬≡∃ A B = isoToPath (iso (¬∀¬≡∃Hlp1 A B) (¬∀¬≡∃Hlp2 A B)
  (λ b → isProp∃ A B (¬∀¬≡∃Hlp1 A B (¬∀¬≡∃Hlp2 A B b)) b)
  (λ a → isProp¬∀ A B (¬∀¬≡∃Hlp2 A B (¬∀¬≡∃Hlp1 A B a)) a))

-- So we have classical ∀ and classical ∃ defined using constructive cubical type theory

-----------------------------
-- Function Extensionality --
-----------------------------

-- Function extensionality is a lemma in Cubical Agda, but it is constructive function
-- extensionality and not classical function extensionality.

-- We expect something like:
classicalFunExt0 : {A : Set ℓ} {B : Set ℓ'} → Type (ℓ-max ℓ ℓ')
classicalFunExt0 {A = A} {B = B} = ∀ (f g : A → B) →
  ISTRUE (∀ (x : A) → ISTRUE (f x ≡ g x)) → ISTRUE (f ≡ g)

-- In order to use constructive funExt we would, however, need this to be:
semiClassicalFunExt : {A : Set ℓ} {B : Set ℓ'} → Type (ℓ-max ℓ ℓ')
semiClassicalFunExt {A = A} {B = B} =
  ∀ (f g : A → B) → ISTRUE (∀ (x : A) → (f x ≡ g x)) → ISTRUE (f ≡ g)

--Proof:
semiClassicalFunExtProof : {A : Set ℓ}{B : Set ℓ'} → semiClassicalFunExt {A = A}{B = B}
semiClassicalFunExtProof {A = A}{B = B} f g = A→B→¬¬A→¬¬B funExt 

-- OK, but we need that inner ISTRUE for classical purposes.
-- It would follow if B had decidable equality, but that would be adding an extra axiom,
-- and not so different from adding LEM!

-- It is preferable to leave extra axioms to the user. It even suggests that classical
-- mathematics may be assuming too much here.

-- We can try weakening the classical version further, but by having more ISTRUEs
-- rather than less:
classicalFunExt1 : {A : Set ℓ} {B : Set ℓ'} → Type (ℓ-max ℓ ℓ')
classicalFunExt1 {A = A} {B = B} =
  ∀ (f g : A → B) →
    ISTRUE ( ISTRUE (∀ (x : A) → ISTRUE (f x ≡ g x)) →
             ISTRUE (f ≡ g) )

-- At this point we know this would be the same as the following
-- (by using ISTRUE∀ twice), which has a maximal number of ISTRUE:
classicalFunExt2 : {A : Set ℓ} {B : Set ℓ'} → Type (ℓ-max ℓ ℓ')
classicalFunExt2 {A = A} {B = B} =
  ISTRUE ((f : A → B) → ISTRUE ((g : A → B) →
    ISTRUE (ISTRUE (∀ (x : A) → ISTRUE (f x ≡ g x)) → ISTRUE (f ≡ g)) ))

-- Can classicalFunExt1 be proven? Or are we stuck with the semi-classical version?

-- The following would be needed to prove classicalFunExt1 from the semi-classical case:
neededFunExt : {A : Set ℓ}{B : Set ℓ'} → Type (ℓ-max ℓ ℓ')
neededFunExt {A = A}{B = B} =
  ∀ (f g : A → B) →
    ISTRUE
      ( ISTRUE (ISTRUE (∀ (x : A) → ISTRUE (f x ≡ g x))) →
        ISTRUE (∀ (x : A) → (f x ≡ g x)) )

-- It doesn't seem to help; Removing the ISTRUE after the ∀ (x : A) continues to elude us. 

-- We have not been able to reproduce a fully classical version of function extensionality,
-- at least not without adding an axiom like The Law Of The Excluded Middle!

-- Something analogous should be the case for bisimilarity of streams.

------------------------------------------------
-- Decidable Codomain Function Extensionality --
------------------------------------------------

-- On the other hand the following does hold:
decidableClassicalFunExt : {A : Set ℓ} {B : Set ℓ'} → Type (ℓ-max ℓ ℓ')
decidableClassicalFunExt {A = A} {B = B} =
   (∀ (b b' : B) →  Dec (b ≡ b')) →
    ∀ (f g : A → B) → ISTRUE (∀ (x : A) → ISTRUE (f x ≡ g x)) → ISTRUE (f ≡ g)

decEqLemma : (∀ (b b' : B) → Dec (b ≡ b')) → ∀ (b b' : B) → (ISTRUE (b ≡ b')) → (b ≡ b')
decEqLemma decidable b b' ist with (decidable b b')  
... | yes Y = Y
... | no N = ⊥-elim (ist N)

decidableClassicalFunExtProof : ∀ (A : Set ℓ) → ∀ (B : Set ℓ') → decidableClassicalFunExt {A = A}{B = B} 
decidableClassicalFunExtProof {ℓ}{ℓ'} A B decidable f g  = A→B→¬¬A→¬¬B λ ab → funExt (step ab) 
  where
    step : ((y : A) → ISTRUE (f y ≡ g y)) → ((x : A) → f x ≡ g x)
    step ist x = decEqLemma decidable (f x) (g x) (ist x)

-- Which is to say if decidable equality exists on the codomains of f and g then
-- the classical version holds. It is interesting that real numbers in constructive
-- mathematics are no decidable in this sense.

--------------------------
-- CLASSICAL EQUALITIES --
--------------------------

-- In the preceding ISTRUE (b ≡ b') was used as a classical equality between b and b'.
-- It is of course just (b ≡ b') wrapped in ISTRUE. We can do this to any constructive
-- type. Any such classical propositions or outer-classically wrapped type is isProp.
-- This gives us a classical equality of propositions, too, ie:
--                 ISTRUE ((ISTRUE A) ≡ (ISTRUE B))
-- which is also:  (ISTRUE A) ≡ (ISTRUE B), so we don't need to be concerned about
-- which is the better classical version when using outer-classical A and B. 
-- Further this is just a classical bijection, as one would expect, levels notwithstanding:

--- By definition:
OuterClassicalDef : ∀ {A : Set ℓ} → OuterClassical A → (ISTRUE A) ≡ A
OuterClassicalDef {ℓ} {A} (invariant x) = x

ClassicalPropositionalEqualityHlp1 : ∀ {A B : Set ℓ} →
  OuterClassical A → OuterClassical B → (ISTRUE ((ISTRUE A) ≡ (ISTRUE B))) → ISTRUE (A ≡ B)
ClassicalPropositionalEqualityHlp1 {ℓ} {A} {B} (invariant oca) (invariant ocb) ist =
  A→B→¬¬A→¬¬B (λ eq → sym oca ∙ (eq ∙ ocb)) ist

ClassicalPropositionalEqualityHlp2 : ∀ {A B : Set ℓ} →
  OuterClassical A → OuterClassical B → ISTRUE (A ≡ B) → (ISTRUE ((ISTRUE A) ≡ (ISTRUE B)))
ClassicalPropositionalEqualityHlp2 {ℓ}{A}{B} oca ocb ist =
  A→B→¬¬A→¬¬B (cong (λ a → ISTRUE a)) ist

-- lemma:
ClassicalPropositionalEquality : ∀ {A B : Set ℓ} →
   OuterClassical A → OuterClassical B →
  (ISTRUE ((ISTRUE A) ≡ (ISTRUE B))) ≡ ISTRUE (A ≡ B)
ClassicalPropositionalEquality {ℓ} {A} {B} (invariant a) (invariant b) =
  isoToPath (iso
    (ClassicalPropositionalEqualityHlp1 (invariant a) (invariant b))
    (ClassicalPropositionalEqualityHlp2 (invariant a) (invariant b))
    (λ b₁ i x → b₁ x) λ a₁ i x → a₁ x)

-- Notice how we need levels to be aligned here for this to work:
ClassicalBijectionLemma1 :  ∀ {A B : Set ℓ} →
  OuterClassical A → OuterClassical B → (ISTRUE (A ≡ B)) ≡ (ISTRUE (Lift (A ⟷ B))) 
ClassicalBijectionLemma1 {ℓ} {A} {B} oca@(invariant oca') ocb@(invariant ocb') =
  sym (ClassicalPropositionalEquality oca ocb) ∙ result 
  where
    step1 : (Lift {i = ℓ}{j = ℓ-suc ℓ} (A ⟷ B)) ≡ (Lift {i = ℓ}{j = ℓ-suc ℓ} ((ISTRUE A) ⟷ (ISTRUE B)))
    step1 = cong (λ x → Lift {i = ℓ}{j = ℓ-suc ℓ} x) (cong₂ (λ a b → a ⟷ b) (sym oca') (sym ocb'))
    step2 : (Lift {i = ℓ}{j = ℓ-suc ℓ} ((ISTRUE A) ⟷ (ISTRUE B))) → ((ISTRUE A) ≡ (ISTRUE B))
    step2 (lift record { AtoB = AtoB₁ ; BtoA = BtoA₁ }) =
      isoToPath (iso AtoB₁ BtoA₁ (λ b i x → b x) λ a i x → a x)
    step3 : ((ISTRUE A) ≡ (ISTRUE B)) → (Lift {i = ℓ}{j = ℓ-suc ℓ} ((ISTRUE A) ⟷ (ISTRUE B)))
    step3 x = lift (record { AtoB = transport x ; BtoA = transport (sym x)})
    step4 : ISTRUE ((ISTRUE A) ≡ (ISTRUE B)) ≡ ISTRUE (Lift {i = ℓ}{j = ℓ-suc ℓ} ((ISTRUE A) ⟷ (ISTRUE B)))
    step4 = isoToPath (iso (A→B→¬¬A→¬¬B step3) (A→B→¬¬A→¬¬B step2) (λ b i x → b x) (λ a i x → a x))
    result : (ISTRUE ((ISTRUE A) ≡ (ISTRUE B))) ≡ (ISTRUE (Lift {i = ℓ}{j = ℓ-suc ℓ} (A ⟷ B)))
    result = step4 ∙ cong (λ x → ISTRUE x) (sym step1)
    
A⟺B≡A⇔B : ∀ {A : Set ℓ} {B : Set ℓ'} → (A ⟺ B) ≡ (A ⇔ B)
A⟺B≡A⇔B {ℓ}{ℓ'}{A}{B} = A⟷BisProps A⟺B⟷A⇔B (isProp'→isProp isProp⟺) (isProp'→isProp isProp⇔)

A⟺B≡¬¬A⟷B :  ∀ {A : Set ℓ} {B : Set ℓ'} → (A ⟺ B) ≡ ¬¬ (A ⟷ B)
A⟺B≡¬¬A⟷B {ℓ}{ℓ'}{A}{B} = A⟷BisProps A⟺B⟷¬¬A⟷B (isProp'→isProp isProp⟺) isProp¬
 
lemma2Hlp : ∀ {A B : Set ℓ} → ISTRUE A ≡ A → ISTRUE B ≡ B →
  (ISTRUE (Lift {i = ℓ}{j = ℓ'} (A ⟷ B))) ≡ (Lift {i = ℓ}{j = ℓ'} (A ⇔ B))
lemma2Hlp {ℓ}{ℓ'}{A}{B} oca ocb = step1 ∙ result 
  where
    step1 : (ISTRUE (Lift {i = ℓ}{j = ℓ'} (A ⟷ B))) ≡ (Lift {i = ℓ}{j = ℓ'} (ISTRUE (A ⟷ B)))
    step1 = Lift-ISTRUE-commutativity
    result : (Lift {i = ℓ}{j = ℓ'} (ISTRUE (A ⟷ B))) ≡ (Lift {i = ℓ}{j = ℓ'} (A ⇔ B))
    result = cong (λ x → Lift {i = ℓ}{j = ℓ'} x) (sym A⟺B≡¬¬A⟷B ∙ A⟺B≡A⇔B)

-- lemma2:
ClassicalBijectionLemma2 : ∀ {A B : Set ℓ} →
  OuterClassical A → OuterClassical B → (ISTRUE (A ≡ B)) ≡ (Lift (A ⇔ B)) 
ClassicalBijectionLemma2 {ℓ} {A} {B} (invariant oca) (invariant ocb) =
  ClassicalBijectionLemma1 (invariant oca) (invariant ocb) ∙ (lemma2Hlp oca ocb)

-- Nevertheless metatheoretic proofs, such as two operators being equivalent,
-- such that they are inter-changeable via transport, requires the constructive
-- cubical equality.
----------------------------------------------
