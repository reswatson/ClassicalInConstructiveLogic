
{-# OPTIONS --safe #-} 
{-# OPTIONS --cubical-compatible #-}

module Logic.LawOfExcludedMiddle where

open import Agda.Primitive 
open import Level renaming (_⊔_ to lmax)

open import Data.Empty
open import Relation.Nullary
open import Data.Sum 
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Logic.Classical.Base
open import Logic.Classical.Properties

private 
  variable
   ℓ ℓ' ℓ'' ℓ'''  : Level

private
  variable
    A : Set ℓ
    B : Set ℓ'
    C : Set ℓ''
    D : Set ℓ'''

--------------------------------
-- Law Of The Excluded Middle --
--------------------------------

-- A note on the Law of the Excluded Middle and its relation to decidability.
-- The univalence compatible version is given here with an isProp A argument.
-- Univalence requires this for compatibility.

LEM : {ℓ : Level} -> Set (lsuc ℓ)  
LEM {ℓ} = ∀ (A : Set ℓ) -> isProp A -> Dec' {ℓ} A  
  -- incidentally, this suggests that propositions should be isProp

-- This shows the consistency of using LEM:
¬¬LEM : {ℓ : Level} -> Set (lsuc ℓ) 
¬¬LEM {ℓ} = ¬¬ (LEM {ℓ})

∀LEM : Setω
∀LEM = (∀ ℓ → LEM {ℓ})

LEM→Dec' : (A : Set ℓ) -> isProp A -> LEM {ℓ} -> Dec' {ℓ} A
LEM→Dec' A ispa lem = lem A ispa

Dec'→LEM : (∀ (A : Set ℓ) -> isProp A ->  Dec' {ℓ} A) -> LEM {ℓ}
Dec'→LEM  = λ z → z 

LEM→ExcludedMiddle : {A : Set ℓ} -> isProp A -> LEM {ℓ} -> A ⊎ (¬ A)
LEM→ExcludedMiddle {ℓ} {A} ispa lem with (lem A ispa)
...                         | Yes a = inj₁ a
...                         | No ¬a = inj₂ ¬a

LEM→DoubleNeg : ∀ {A : Set ℓ} -> LEM {ℓ} -> isProp A -> (¬¬ A) -> A
LEM→DoubleNeg {ℓ} {A} lem ispA x with (lem A ispA)
...                      | Yes A = A
...                      | No A = ⊥-elim contra
                              where
                               contra : ⊥
                               contra = x A

Dec'→¬¬A→A : {A : Set ℓ} -> Dec' A -> ((¬¬ A) → A)
Dec'→¬¬A→A {ℓ} {A} (Yes p) x = p
Dec'→¬¬A→A {ℓ} {A} (No ¬p) x = ⊥-elim (x ¬p)

-- How decidability of all Set ℓ implies classical logic:
decidability→LEM : {ℓ : Level} → (∀ {Q : Set ℓ} → Dec' Q) → LEM {ℓ} 
decidability→LEM {ℓ} dcQ A ispA = dcQ

-- ...also when restricted only to those Set ℓ which are isProp:
decidableProp→LEM : {ℓ : Level} → (∀ {Q : Set ℓ} → isProp Q → Dec' Q) → LEM {ℓ} 
decidableProp→LEM {ℓ} dcQ A ispA = dcQ ispA

-----------------------------------
-- Some extra notes:

A→B→C'→B→A→C : {A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → (A → B → C) → B → A → C
A→B→C'→B→A→C {ℓ}{ℓ'}{ℓ''}{A}{B}{C} ABC b a = ABC a b

¬¬A→¬¬B→C'→¬¬'B→A→C : {A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → ((¬¬ A) → (¬¬ (B → C))) → ¬¬ (B → A → C)
¬¬A→¬¬B→C'→¬¬'B→A→C {ℓ}{ℓ'}{ℓ''}{A}{B}{C} nnA = A→B→¬¬A→¬¬B A→B→C'→B→A→C (¬¬A→¬¬B'→¬¬A→B nnA)

¬¬markovAHlp : ∀ {A : Set ℓ} → ∀ (P : A → Set ℓ') → ¬¬ (Σ A P) → ¬¬ ( (∀ (a : A) → ((P a) ⊎ (¬ (P a)))) → Σ A P )
¬¬markovAHlp {ℓ} {ℓ'} {A} P nnE x = nnE (λ z → x (λ z₁ → z))

-- Markov's rule is admissible (double negation of Markov's rule - generalised to all A):
¬¬markovA : ∀ {A : Set ℓ} → ∀ (P : A → Set ℓ') → ¬¬ ( (∀ (a : A) → ((P a) ⊎ (¬ (P a)))) → (¬¬ (Σ A P)) → Σ A P )
¬¬markovA {ℓ} {ℓ'} {A} P = ¬¬A→¬¬B→C'→¬¬'B→A→C (λ x → ¬¬markovAHlp P (¬¬¬A→¬A x))


