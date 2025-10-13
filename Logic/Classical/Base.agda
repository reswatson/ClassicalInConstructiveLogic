{-# OPTIONS --safe #-} 
{-# OPTIONS --cubical-compatible #-}

module Logic.Classical.Base where

open import Agda.Primitive 
open import Level

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum 
open import Data.Product

private 
  variable
   ℓ ℓ' ℓ'' ℓ'''  : Level

private
  variable
    A : Set ℓ
    B : Set ℓ'
  --  C : Set ℓ''
  --  D : Set ℓ'''

--------------------------

isContr : Set ℓ → Set ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Set ℓ → Set ℓ  
isProp A = (x y : A) → x ≡ y

-- Some variations to the original
Π : ∀ {ℓ ℓ'} (B : Set ℓ) (E : B → Set ℓ') → Set (ℓ ⊔ ℓ') 
Π B E = (x : B) → E x

syntax Π B (λ x → E) = Π[ x ∈ B ] E

------------------------------


¬¬ : Set ℓ -> Set ℓ
¬¬ {ℓ} s = ¬ (¬ s)

¬¬A≡¬'¬A : (¬¬ A) ≡ (¬ (¬ A))
¬¬A≡¬'¬A {ℓ} {A} = refl

A→¬¬A :  {A : Set ℓ} → A → ¬ ¬ A
A→¬¬A {ℓ} {A} a na = na a

¬¬¬A→¬A : {A : Set ℓ} → ¬ (¬ (¬ A)) → ¬ A
¬¬¬A→¬A {ℓ}{A} nnA = λ x → nnA (A→¬¬A x)

¬¬A→B'→¬¬A→¬¬B : (¬ (¬ (A → B))) → (¬ (¬ A)) → (¬ (¬ B))
¬¬A→B'→¬¬A→¬¬B  = λ z z₁ z₂ → z₁ (λ z₃ → z (λ z₄ → z₂ (z₄ z₃)))

converse : (A -> B) -> (¬ B) -> (¬ A)  
converse ABC nB x = nB (ABC x)

double-converse : (A -> B) -> (¬ (¬ A)) -> (¬ (¬  B))
double-converse AB = converse (converse AB)

A→B→¬¬A→¬¬B = double-converse

¬¬⊥→⊥ : (¬ (¬ ⊥)) → ⊥
¬¬⊥→⊥ x = ⊥-elim (x (λ ()))

data Dec' (P : Set ℓ) : Set ℓ where
  Yes : ( p :   P) → Dec' {ℓ} P
  No  : (¬p : ¬ P) → Dec' {ℓ} P

Dec'A→A'OR'¬A : Dec' A → A ⊎ (¬ A)
Dec'A→A'OR'¬A (Yes a) = inj₁ a
Dec'A→A'OR'¬A (No ¬a) = inj₂ ¬a

-- a constructive bijection, logical equivalence of Types as propositions:
record _⟷_ (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  field
    AtoB : A → B
    BtoA : B → A

open _⟷_ public

-- Section and retract
module sections {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  section : (f : A → B) → (g : B → A) → Set ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction
  retract : (f : A → B) → (g : B → A) → Set ℓ
  retract f g = ∀ a → g (f a) ≡ a

open sections public

-- a constructive Set isomorphism
record Iso (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : section fun inv
    leftInv  : retract fun inv

open Iso public

A⟷BisPropAisProp→IsoAB : {A : Set ℓ} {B : Set ℓ'} -> A ⟷ B -> isProp A -> isProp B -> Iso A B
A⟷BisPropAisProp→IsoAB {ℓ}{ℓ'}{A}{B} AB ispA ispB = iso (AB .AtoB) (AB .BtoA) (λ b → ispB (AB .AtoB (AB .BtoA b)) b)
                                                     (λ a → ispA (AB .BtoA (AB .AtoB a)) a)

---------------------------------------------------------------
-- Classical Propositional Logic Is Constructed From Scratch --
---------------------------------------------------------------

-- This defines what is essentially a Godel fragment.

-- Take the following definitions from constructive type theory:

NOT = ¬_
FALSE = ⊥

-- We define a notion of true that is non-falsifiability in
-- constructive logic, but which has a classical flavour:

TRUE = NOT FALSE
ISTRUE = ¬¬

-- We add a custom 'arrow', again with a classical flavour:

_⇒_ :  (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ')
A ⇒ B = (¬¬ A) → (¬¬ B)

-- From this we can construct the Godel fragment of classical logic within the MLTT variant 
-- of Agda, maintaining cubical-compatibility. The classical propositional operators
-- are to be constructed solely in terms of FALSE, ISTRUE and_⇒_, plus, in analysing
-- the semantics, the atoms will be assumed to be decidable. In order to stay within
-- the classical fragment we must obey these rules.

-- We now proceed by using the abbreviations of Robbin's D1 - D4 to show that
-- classical logic follows. What Robbin considers an abbreviation is here
-- a definition.

-- D1:
NOT' : Set ℓ → Set ℓ
NOT' A = (A ⇒ FALSE)

-- D2:
OR' : Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
OR' A B = (NOT' A) ⇒ B

-- D3:
AND' :  Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
AND' A B = NOT' (OR' (NOT' A) (NOT' B)) 

-- D4 (classical propositional equality, classical bijection): 
_⇔_ : {ℓ ℓ' : Level} → Set ℓ -> Set ℓ' -> Set (ℓ ⊔ ℓ')
_⇔_ A B = AND' (A ⇒ B) (B ⇒ A)  

-- Inductive decidable semantics.
-- We assume all Atoms are decidable as per V1 in Robbin where decidabilty is assumed
-- implicitly. V1 (Robbin) states  that V(pᵢ ) is already defined for i = 1, 2, ...,
-- which is to say they are decided and thus decidable. Later, when using Cubical Agda,
-- we will make this far more general, but for now we show that the properties of
-- Classical propositional calculus are replicated...

-- Decidability gives us a double-negation rule for Atoms:
Dec'A→ISTRUEA→A : Dec' A → ISTRUE A → A
Dec'A→ISTRUEA→A (Yes a) ista = a
Dec'A→ISTRUEA→A (No ¬a) ista = ⊥-elim (ista ¬a)

-- And wrapping such an Atom in the classical operators such as ISTRUE also yields a
-- decidable proposition:
Dec'Atom : Dec' A → Dec' (ISTRUE A)
Dec'Atom {ℓ} {A} (Yes p) = Yes λ z → z p    -- Yes p is Robbin's 1 value assignment
Dec'Atom {ℓ} {A} (No ¬p) = No (λ z → z ¬p)  -- No p is Robbin's 0 value assignment

-- Further, Atoms wrapped in ISTRUE are isProp, whereas this is not pre-defined for any A:
isPropAtom : {A : Set ℓ} → isProp (ISTRUE A)
isPropAtom {ℓ}{A} = λ x y → refl

-- V2 of Robbin:
V2 : Dec' FALSE
V2 = No λ ()

-- V3 of Robbin
V3 : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → Dec' A → Dec' B → Dec' (A ⇒ B) 
V3 {ℓ} {ℓ'} {A} {B} (Yes p) (Yes p₁) = Yes (λ z z₁ → z₁ p₁)
V3 {ℓ} {ℓ'} {A} {B} (Yes p) (No ¬p) = No (λ z → z (λ z₁ → z₁ p) ¬p)
V3 {ℓ} {ℓ'} {A} {B} (No ¬p) (Yes p) = Yes (λ z z₁ → z₁ p)
V3 {ℓ} {ℓ'} {A} {B} (No ¬p) (No ¬p₁) = Yes (λ z z₁ → z ¬p)

-- And all of Robbin's criteria are met.

-- Necessarily we get the Law of The Excluded Middle, which implies double negation,
-- it's just that this is the classical OR' and not the usual constructive 'or' (ie  ⊎)
-- as used in Agda.

ClassicalExcludedMiddle : {A : Set ℓ} → OR' A (NOT' A)
ClassicalExcludedMiddle {ℓ} {A} = λ x y → x y 

-- By the simple combination of such operators we can define the whole of classical
-- propositional logic.

-----------------------

-- Further, we have the following constructive logical equivalence, and thus a further
-- D1-style 'abbreviation' outside of the classical logic proper fragment:

D1 : (NOT A) ⟷ (NOT' A)  
D1 {ℓ}{A} = record { AtoB = λ z z₁ z₂ → z₁ z ; BtoA = λ x → λ a → x (A→¬¬A a) (λ f → f) }

D1L : NOT A → NOT' A
D1L nA = λ z z₁ → z nA

D1R : NOT' A → NOT A
D1R {ℓ}{A} = BtoA D1

-- This shows how constructive logic, the constructive logical equivalence of bijection
-- _⟷_ , can be used to provide a metatheoretic proof about classical logic, in this case
-- that the two definitions of logical negation are constructively logically equivalent and are
-- both classical logical negations, even if NOT is not in the classical logic proper fragment!

-- We actually have the stronger correspondence of (constructive) isomorphism:
IsoD1 : Iso (NOT A) (NOT' A)
IsoD1 {ℓ}{A} = A⟷BisPropAisProp→IsoAB D1 (λ x y → refl) (λ x y → refl)
-- the two (λ x y → refl) entries are proofs that the terms NOT A and NOT' A are isProp 

-- All the propositions and propositional operators are isProp in the following sense:

isProp⇒ : {A : Set ℓ} -> {B : Set ℓ'} -> isProp (A ⇒ B)
isProp⇒ {ℓ}{ℓ'}{A}{B} = λ x y → refl

isProp¬ : isProp (¬ A)
isProp¬ = λ x y → refl

isPropNOT : isProp (NOT A)
isPropNOT = isProp¬

isPropNOT' : isProp (NOT A)
isPropNOT' = λ x y → refl

isProp⇔ : {A : Set ℓ} -> {B : Set ℓ'} -> isProp (A ⇔ B)
isProp⇔ {ℓ}{ℓ'}{A}{B} = λ x y → refl

isPropFALSE : isProp FALSE
isPropFALSE = λ ()
 
-- and so on (also inductively)

-- Being classical they are all invariant under double-negation too:

¬¬Invariant⇒ :  {A : Set ℓ} -> {B : Set ℓ'} -> ¬¬ (A ⇒ B) → (A ⇒ B)
¬¬Invariant⇒ = λ z z₁ z₂ → z₁ (λ z₃ → z (λ z₄ → z₄ (λ z₅ → z₅ z₃) z₂))

¬¬Invariant¬ : {A : Set ℓ} -> ¬¬ (¬ A) → ¬ A
¬¬Invariant¬ = λ z z₁ → z (λ z₂ → z₂ z₁)

¬¬InvariantNOT : {A : Set ℓ} -> ¬¬ (NOT A) → NOT A
¬¬InvariantNOT = λ z z₁ → z (λ z₂ → z₂ z₁)

¬¬InvariantNOT' :  {A : Set ℓ} -> ¬¬ (NOT' A) → NOT' A
¬¬InvariantNOT' nnna = D1L (¬¬InvariantNOT (A→B→¬¬A→¬¬B D1R nnna))  

¬¬InvariantFALSE : ¬¬ FALSE → FALSE
¬¬InvariantFALSE nnf = ¬¬⊥→⊥ nnf

-- and, again, so on also by induction. 

------------------------------------

-- The following lemma shows just how important _⟷_ is to the constructions here; it enables us
-- to make inductive arguments based on logically equivalent substitutions:

SUBST⟷-lemma : (OP : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> (OP' : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> ({ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → (OP A B) ⟷ (OP' A B))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⟷ C) → (B ⟷ D) → ((OP A B) ⟷ (OP C D)))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⟷ C) → (B ⟷ D) → ((OP' A B) ⟷ (OP' C D)))
SUBST⟷-lemma OP OP' OP⟷OP' substOP {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD = record { AtoB = λ z → OP⟷OP' .AtoB (substOP AC BD .AtoB (OP⟷OP' .BtoA z)) ; BtoA = λ z → OP⟷OP' .AtoB (substOP AC BD .BtoA (OP⟷OP' .BtoA z)) }

-- This is strengthened when 'propositions' are isProp, as then  _⟷_ is logically
-- equivalent to an isomorphism as per A⟷BisPropAisProp→IsoAB. As such we also
-- get a corollary:
isPropIso :  {A : Set ℓ} -> {B : Set ℓ'} -> isProp A -> Iso A B → isProp B
isPropIso {ℓ} {ℓ'} {A} {B} isp (iso fun inv rightInv leftInv) x y = trans (sym fgx) (trans xy fgy)
                                                 where
                                                  ix : (inv x) ≡ inv y
                                                  ix = isp (inv x) (inv y)
                                                  fgx : fun (inv x) ≡ x
                                                  fgx = rightInv x
                                                  fgy : fun (inv y) ≡ y
                                                  fgy = rightInv y
                                                  xy = cong fun ix

-- All the classical logical operators above result in isProp terms, so equivalences
-- between any such operators constructed within the classical fragment (and with arguments applied)
-- are also isomorphisms, notwithstanding level subtleties. In other cases (outside the classical
-- logic proper fragment) we can prove an isomoprhism only by proving both the logical equivalence
-- and that the newly constructed operator is isProp. This is seen in IsoD1 for NOT A and NOT' A,
-- where the term that is not in the fragment was NOT A and also needed an isProp proof. IsoD1 resulted.

-- Operators that result in isProp terms when their arguments are given are used, though the
-- substitution lemma SUBST⟷-lemma doesn't actually require this. Operators may be considered
-- logically equivalent, just like propositions, if they result in logically equivalent terms:
-- eg using D1 we can say that NOT and NOT' are logically equivalent.

-- However, when forming an Iso, rather than just a logical equivalence, we may prefer to bump the
-- levels in some cases, so that they become the same on both sides of ⟷. It's really isomorphism
-- between Types of the same level that characterises true interchangeable equivalence by substitution,
-- as this becomes computational when using Cubical Agda; it becomes Cubical equality. 

-- Level bumping: 
liftLeft⟷ : {ℓ : Level} → A ⟷ B → (Lift (lsuc ℓ) A) ⟷ B
liftLeft⟷ {ℓ}{ℓ'} AB = record
                       { AtoB = λ z → AB .AtoB (z .lower)
                       ; BtoA = λ z → lift (AB .BtoA z)}

-- Some properties of _⟷_
A⟷C→B⟷D→A⟷B⟷C⟷D :  {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} → (A ⟷ C) → (B ⟷ D) → (A ⟷ B) ⟷ (C ⟷ D)
A⟷C→B⟷D→A⟷B⟷C⟷D {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD = record { AtoB = λ z → record
   { AtoB = λ z₁ → BD .AtoB (z .AtoB (AC .BtoA z₁)) ; BtoA = λ z₁ → AC .AtoB (z .BtoA (BD .BtoA z₁))} ;
     BtoA = λ z → record { AtoB = λ z₁ → BD .BtoA (z .AtoB (AC .AtoB z₁)) ; BtoA = λ z₁ → AC .BtoA (z .BtoA (BD .AtoB z₁))} }

refl⟷ : A ⟷ A
refl⟷ = record { AtoB = λ z → z ; BtoA = λ z → z }

trans⟷ : {ℓ ℓ' ℓ'' : Level} → {A : Set ℓ} → {B : Set ℓ'} → {C : Set ℓ''} → (A ⟷ B) → (B ⟷ C) → (A ⟷ C)
trans⟷ {ℓ}{ℓ'}{ℓ''} AB BC = record { AtoB = λ z → BC .AtoB (AB .AtoB z) ; BtoA = λ z → AB .BtoA (BC .BtoA z) }

sym⟷ : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → (A ⟷ B) → (B ⟷ A)
sym⟷ {ℓ}{ℓ'}{A}{B} AB = record { AtoB = AB .BtoA ; BtoA = AB .AtoB }

isProp⟷ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → isProp (A → B) → isProp (B → A) → isProp (A ⟷ B)
isProp⟷ {ℓ} {ℓ'} {A} {B} ispa ispb record { AtoB = AtoB1 ; BtoA = BtoA1 } record { AtoB = AtoB2 ; BtoA = BtoA2 } with ispa AtoB1 AtoB2
... | refl with ispb BtoA1 BtoA2 
... | refl = refl

