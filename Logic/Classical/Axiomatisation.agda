
{-# OPTIONS --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Logic.Classical.Axiomatisation where

open import Relation.Nullary
open import Data.Empty

open import Logic.Classical.Base
  renaming (isProp to isProp' ; isProp¬ to isProp¬') hiding (Iso ; section ; retract) 
open import Logic.Classical.Properties hiding (transport)
open import Logic.Conversions
open import Logic.Classical.Predicates
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

private 
  variable
    ℓ ℓ' ℓ'' : Level
private
  variable
    A : Set ℓ
    B : Set ℓ'


----------------------------------
-- AXIOMS OF PREDICATE CALCULUS --
----------------------------------

-- Contrary to Logic.Classical.Base and Logic.Classical.Properties, here
-- the assumption made for Atoms will be that they are Outer Classical
-- as in Logic.Classical.Predicates. This is more generalised than might
-- be usual, in that Classical statements can then be made about
-- constructive propositions - they just need to be correctly 'wrapped'
-- in a double-negative, here an 'ISTRUE', and then classical predicate
-- calculus can be used as if they were atoms.

-- The aim here is to show how the axioms of classical predicate logic
-- are satisfied by ∀ and ∃ as defined in Logic.Classical.Predicates,
-- the use of classical propositional calculus having been already
-- defined and demonstrated. Note that the ∃ is the classical version,
-- ie ¬∀¬, but the ∀ is the same for both classical and constructive logic.

-- This approach can be called 'classical in constructive', as,
-- fundamentally we are constraining constructive logic to a classical
-- fragment.

-- One less than fully classical consequence of this is the function
-- extensionality principle remaining constructive as a result; as discussed
-- in Classical.Logic.Predicates. This highlights that the real difference
-- between classical and constructive logic are not the main block to
-- reproducing classical mathematics *natively* withing constructive
-- Type theories. Rather the first problem one comes up against is that
-- real numbers as defined constructively do not have decidable equality,
-- and as such function extensionality is not available in its full
-- classical form.

-- [Speculation] Maybe this is because classical function
-- extensionality is deficient? But it isn't classical logic versus
-- constructive logic doing this, as perhaps indicated first by Goedel's
-- fragment. For those who must use such an axiom it can be added by hand;
-- a weaker addition than adding the Law Of The Excluded Middle. One might
-- for example add decidable equality of reals as an axiom to much the
-- same effect. The only trouble is: it isn't constructively true, meaning
-- it doesn't follow from the data structures used!

-- In any case the law of the excluded middle needs to be in the form
-- as given in Logic.LawOfExcludedMiddle for certain consistency with
-- Cubical Agda. By using the Law Of The Excluded Middle as an axiom,
-- the "classical in constructive" approach is rendered moot. It isn't
-- the objective here to use *any* non-constructive axioms in implementing
-- classical logic! 

-- Four more axioms are needed for classical predicate calculus:
-- [Kleene] S.C. Kleene, "Introduction to metamathematics" , North-Holland (1951)
-- We use [Kleene] section 19, page 82. Group A2, starting at rule-9.
-- Axioms 1-8 are for classical propositional calculus, but this is already shown.
-- Where we need to we can assume 'input' propositions are outer classical,
-- eg (A x) below.

-- Kleene:
-- "x is a variable"   => x is a term of a type X
-- "A(x) is a formula" => A is a predicate on type X
-- "C is a formula which does not contain x free" => C is a type
-- "t is a term which is free for x in A(x)" => t is a term of type X
-- So we take it that type theory interprets a variable to be just a
-- term of type X.

rule-9 : (X : Set ℓ) → (A : X → Set ℓ') → (C : Set ℓ'') →
  (oca : ∀ (x : X) → OuterClassical (A x)) → 
  (∀ (x : X) → (C ⇒ (A x))) → (C ⇒ (∀ (x : X) → (A x)))
rule-9 X A C oca Ax nnc = λ x → ⊥-elim (x step3)
  where
    step1 : ∀ (x : X) → ISTRUE (A x)
    step1 x = (Ax x) nnc
    step2 : ∀ (x : X) → ISTRUE (A x) ≡ A x
    step2 x = extract-invariant (oca x)
    step3 : ∀ (x : X) → A x
    step3 x = transport (step2 x) (step1 x) 

-- This one barely needs to be stated in type theory:
rule-10 : (X : Set ℓ) → (A : X → Set ℓ') → ∀ (t : X) → (∀ (x : X) → A x) ⇒ (A t)
rule-10 X A t = λ z z₁ → z (λ z₂ → z₁ (z₂ t))

rule-11 : (X : Set ℓ) → (A : X → Set ℓ') → ∀ (t : X) → (A t) ⇒ ∃ X (λ x → A x) 
rule-11 {ℓ}{ℓ'} X A t At = λ z → z (λ z₁ → At (λ z₂ → z₁ (t , z₂)))

rule-12 :
  (X : Set ℓ) →
  (A : X → Set ℓ') → (∀ (x : X) → OuterClassical (A x)) →
  (C : Set ℓ'') → OuterClassical C →
  (∀ (x : X) → (A x ⇒ C)) → (∃ X A) ⇒ C
rule-12 {ℓ} {ℓ'} {ℓ''} X A oca C occ AxC nn∃x = A→B→¬¬A→¬¬B step3 ∃x
    where
      step1 : Σ X A → ISTRUE C
      step1 s = AxC (s .fst) (λ z → z (s .snd))
      ∃x : ISTRUE (Σ X A)
      ∃x = ¬¬¬A→¬A nn∃x
      step2 : ISTRUE C ≡ C
      step2 = extract-invariant occ
      step3 :  Σ X A → C
      step3 s = transport step2 (step1 s)  

-------------------

