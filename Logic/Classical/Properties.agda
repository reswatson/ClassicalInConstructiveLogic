{-# OPTIONS --safe #-} 
{-# OPTIONS --cubical-compatible #-}

module Logic.Classical.Properties where

open import Agda.Primitive 
open import Level

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum 
open import Data.Product

open import Logic.Classical.Base

private 
  variable
   ℓ ℓ' ℓ'' ℓ'''  : Level

private
  variable
    A : Set ℓ
    B : Set ℓ'
    C : Set ℓ''
    D : Set ℓ'''

--------------------------
-- identity function
id : A → A
id x = x

-- explicit version
idp : {ℓ : Level} {A : Set ℓ} (x : A) → x ≡ x
idp x = refl {x = x}

transport : ∀{ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A}
            (p : x ≡ y) → P x → P y
transport P refl = id

¬¬fst : {A : Set ℓ} -> {B : Set ℓ'} ->  ¬¬ (A × B) -> ¬¬ A
¬¬fst {ℓ}{ℓ'}{A}{B} nnAB x = ¬¬A→B'→¬¬A→¬¬B (A→¬¬A proj₁) nnAB x

¬¬snd : {A : Set ℓ} -> {B : Set ℓ'} ->  ¬¬ (A × B) -> ¬¬ B
¬¬snd {ℓ}{ℓ'}{A}{B} nnAB x = ¬¬A→B'→¬¬A→¬¬B (A→¬¬A proj₂) nnAB x

¬¬×-def : {A : Set ℓ} -> {B : Set ℓ'} -> ¬¬ A → ¬¬ B → ¬¬ (A × B)
¬¬×-def {ℓ}{ℓ'}{A}{B} nna nnb = λ z → nna (λ z₁ → nnb (λ z₂ → z (z₁ , z₂)))

double-transport : {A B : Set ℓ} → A ≡ B -> A ⟷ B
double-transport refl = record { AtoB = λ z → z ; BtoA = λ z → z }

transport≡ : {A B : Set ℓ} → A ≡ B -> A -> B
transport≡ refl a = a

transport' : {A B : Set ℓ} → A ≡ B -> B -> A
transport' refl b = b

¬¬A⟷C→¬A⟷C'⟷⊥ : (¬¬ (A ⟷ C)) -> (¬ (A ⟷ C)) ⟷ ⊥
¬¬A⟷C→¬A⟷C'⟷⊥ nnAC = record { AtoB = nnAC ; BtoA = λ () }

-- lemma for pushing ¬¬ through ∀
¬¬A→B'→¬¬A→¬¬B-dep : {A : Set ℓ} → {B : A → Set ℓ'} → ¬¬ ((x : A) → B x) → (x' : A) → ¬¬ (B x')
¬¬A→B'→¬¬A→¬¬B-dep {ℓ}{ℓ'}{A}{B} x y z = x (λ w → z (w y))

¬¬A→B'→¬¬A→¬¬B-dep2 : {A C : Set ℓ} → {B : A → C → Set ℓ'} →
  ¬¬ ((x : A) (y : C)  → B x y) → (x' : A) (y' : C) → ¬¬ (B x' y')
¬¬A→B'→¬¬A→¬¬B-dep2 {ℓ}{ℓ'}{A}{C} {B} x y z =  ¬¬A→B'→¬¬A→¬¬B-dep (¬¬A→B'→¬¬A→¬¬B-dep x y) z

¬¬A→¬¬B'→¬¬A→¬¬B-dep : {A : Set ℓ} → {B : A → Set ℓ'} → ¬¬ ((x : A) → ¬¬ (B x)) → (x' : A) → ¬¬ (B x')
¬¬A→¬¬B'→¬¬A→¬¬B-dep {ℓ}{ℓ'}{A}{B} x y z = x (λ w → w y z)

¬A→B→A→¬B : {A : Set ℓ} → {B : Set ℓ'} → ¬ (A → B) → (A → ¬ B)
¬A→B→A→¬B = λ z _ z₁ → z (λ _ → z₁)

¬¬'¬¬A→¬¬B : {A : Set ℓ} → {B : Set ℓ'} → ¬¬ (¬¬ A → ¬¬ B) -> ¬¬ A -> ¬¬ B
¬¬'¬¬A→¬¬B {ℓ}{ℓ'} {A = A} {B = B} ist istA = ¬¬¬A→¬A (step (λ x → x istA)) 
  where
    step : ¬¬ (¬¬ A) → ¬¬ (¬¬ B)
    step = ¬¬A→B'→¬¬A→¬¬B ist

AtoB'-¬¬ : ¬¬ (A ⟷ B) -> ¬¬ (A -> B)
AtoB'-¬¬ ist x = A→B→¬¬A→¬¬B AtoB ist x

AtoB''-¬¬ : ¬¬ (¬¬ A ⟷ ¬¬ B) -> ¬¬ (¬¬ A -> ¬¬ B)
AtoB''-¬¬ ist x = A→B→¬¬A→¬¬B AtoB ist x

BtoA'-¬¬ : ¬¬ (A ⟷ B) -> ¬¬ (B -> A)
BtoA'-¬¬ ist x = A→B→¬¬A→¬¬B BtoA ist x

¬¬A⟷B¬¬A⟷¬¬B : ¬¬ (A ⟷ B) -> (¬¬ A) ⟷ (¬¬ B)
¬¬A⟷B¬¬A⟷¬¬B ab = record { AtoB = ¬¬A→B'→¬¬A→¬¬B (AtoB'-¬¬ ab) ; BtoA = ¬¬A→B'→¬¬A→¬¬B (BtoA'-¬¬ ab) }

¬¬A⟷B¬¬B⟷¬¬A : ¬¬ (A ⟷ B) -> (¬¬ B) ⟷ (¬¬ A)
¬¬A⟷B¬¬B⟷¬¬A ab = record { AtoB = ¬¬A→B'→¬¬A→¬¬B (BtoA'-¬¬ ab) ; BtoA = ¬¬A→B'→¬¬A→¬¬B (AtoB'-¬¬ ab) }

BtoA''-¬¬ : ¬¬ (¬¬ A ⟷ ¬¬ B) -> ¬¬ (¬¬ B -> ¬¬ A)
BtoA''-¬¬ ist x = A→B→¬¬A→¬¬B BtoA ist x

¬¬A⟷¬¬B-def :  (¬¬ (¬¬ A ⟷ ¬¬ B)) ⟷ (¬¬ A ⟷ ¬¬ B)
¬¬A⟷¬¬B-def = record { AtoB = λ x → record { AtoB = ¬¬'¬¬A→¬¬B (AtoB''-¬¬ x) ;
                                              BtoA = λ y → ¬¬'¬¬A→¬¬B (BtoA''-¬¬ x) y } ;
                                              BtoA = λ x → A→¬¬A x }

¬¬A⟷¬¬B-def' :  (¬¬ (¬¬ A ⟷ ¬¬ B)) → (¬¬ A ⟷ ¬¬ B)
¬¬A⟷¬¬B-def' = AtoB ¬¬A⟷¬¬B-def 

A⟷B→¬¬A⟷¬¬B : (A ⟷ B) → (¬¬ A) ⟷ (¬¬ B) 
A⟷B→¬¬A⟷¬¬B record { AtoB = AtoB ; BtoA = BtoA } = record { AtoB = A→B→¬¬A→¬¬B AtoB ; BtoA = A→B→¬¬A→¬¬B BtoA }

A≡B→A⟷B : A ≡ B -> A ⟷ B
A≡B→A⟷B refl = record { AtoB = λ z → z ; BtoA = λ z → z }

¬¬'¬¬A≡¬¬B→¬¬'¬¬A⟷¬¬B : ¬¬ (¬¬ A ≡ ¬¬ B) →  ¬¬ (¬¬ A ⟷ ¬¬ B)
¬¬'¬¬A≡¬¬B→¬¬'¬¬A⟷¬¬B {A = A}{B = B} nnAnnB = A→B→¬¬A→¬¬B A≡B→A⟷B nnAnnB

¬¬A≡B→¬¬'¬¬A≡¬¬B :  ¬¬ (A ≡ B) → ¬¬ ((¬¬ A) ≡ (¬¬ B))
¬¬A≡B→¬¬'¬¬A≡¬¬B {A = A}{B = B} nnAB = A→B→¬¬A→¬¬B (λ x → cong (λ y → ¬¬ y) x) nnAB

¬¬cong : {A B : Set ℓ} -> (f : Set ℓ → Set ℓ') -> ¬¬ (A ≡ B) -> ¬¬ (f A ≡ f B) 
¬¬cong {ℓ}{A}{B} f nnab = A→B→¬¬A→¬¬B (cong f) nnab

A⟷B→¬¬'¬¬A⟷¬¬B : A ⟷ B → ¬¬ ((¬¬ A) ⟷ (¬¬ B))
A⟷B→¬¬'¬¬A⟷¬¬B AB = (BtoA ¬¬A⟷¬¬B-def) (A⟷B→¬¬A⟷¬¬B AB)

A→B→C→¬¬A→¬¬B→¬¬C : {A : Set ℓ} → {B : Set ℓ'} -> {C : Set ℓ''} → (A → B → C) → (¬¬ A → ¬¬ B → ¬¬ C)
A→B→C→¬¬A→¬¬B→¬¬C {ℓ}{ℓ'}{ℓ''} {A = A}{B = B}{C = C} abc a b x = step3 x
                         where
                           step1 : ¬¬ A -> ¬¬ (B → C)
                           step1 = double-converse abc
                           step2 : ¬¬ (B → C)
                           step2 = step1 a
                           step3 : ¬¬ C
                           step3 = ¬¬A→B'→¬¬A→¬¬B step2 b

A→B→C→D→¬¬A→¬¬B→¬¬C→¬¬D : {A : Set ℓ} → {B : Set ℓ'} -> {C : Set ℓ''} -> {D : Set ℓ'''}  →
  (A → B → C → D) → (¬¬ A → ¬¬ B → ¬¬ C → ¬¬ D)
A→B→C→D→¬¬A→¬¬B→¬¬C→¬¬D {A = A}{B = B}{C = C}{D = D} abcd a b c x = step3 x
                         where
                           step :  ¬¬ A -> ¬¬ (B → C → D)
                           step = A→B→¬¬A→¬¬B abcd
                           step2 : ¬¬ (B → C → D)
                           step2 = step a
                           step3 : ¬¬ D
                           step3 = ¬¬A→B'→¬¬A→¬¬B (¬¬A→B'→¬¬A→¬¬B step2 b) c


A→B→C→¬¬D→¬¬A→¬¬B→¬¬C→¬¬D : {A : Set ℓ} → {B : Set ℓ'} -> {C : Set ℓ''} -> {D : Set ℓ'''}  →
  (A → B → C → ¬¬ D) → (¬¬ A → ¬¬ B → ¬¬ C → ¬¬ D)
A→B→C→¬¬D→¬¬A→¬¬B→¬¬C→¬¬D {A = A}{B = B}{C = C}{D = D} abcd a b c x = (¬¬¬A→¬A step3) x
                         where
                           step3 : ¬¬ (¬¬ D)
                           step3 = A→B→C→D→¬¬A→¬¬B→¬¬C→¬¬D abcd a b c

¬¬transport : ¬¬ (A ≡ B) → (¬¬ A) → (¬¬ B)
¬¬transport {ℓ}{A}{B} nnab nna = A→B→C→¬¬A→¬¬B→¬¬C transport≡ nnab nna

¬A→¬A×B : ¬ A → ¬ (A × B)
¬A→¬A×B nA (x , y) = nA x

¬B→¬A×B : ¬ B → ¬ (A × B)
¬B→¬A×B nB (x , y) = nB y

¬A⊎B→¬A : {A : Set  ℓ} -> {B : Set  ℓ'} -> ¬ (A ⊎ B) -> (¬ A) 
¬A⊎B→¬A nab x =  nab (inj₁ x)

¬A⊎B→¬B :  {A : Set  ℓ} ->  {B : Set  ℓ'} ->  ¬ (A ⊎ B) -> (¬ B) 
¬A⊎B→¬B nab x =  nab (inj₂ x)

¬A⊎B→¬A×¬B : {A : Set  ℓ} -> {B : Set  ℓ'} -> ¬ (A ⊎ B) -> (¬ A) × (¬ B)
¬A⊎B→¬A×¬B nab = (¬A⊎B→¬A nab) , (¬A⊎B→¬B nab)

¬A×¬B→¬A :  {A : Set  ℓ} ->  {B : Set  ℓ'} -> (¬ A) × (¬ B) -> (¬ A)
¬A×¬B→¬A nanb = proj₁ nanb

¬A×¬B→¬A⊎B : {A : Set  ℓ} -> {B : Set  ℓ'} -> (¬ A) × (¬ B) -> ¬ (A ⊎ B)  
¬A×¬B→¬A⊎B nanb (inj₁ x) = proj₁ nanb x
¬A×¬B→¬A⊎B nanb (inj₂ y) = proj₂ nanb y

¬¬A×B→¬¬A :  {A : Set ℓ} → {B : Set ℓ'} → ¬ ¬ (A × B) → ¬ ¬ A 
¬¬A×B→¬¬A {ℓ} {ℓ'} {A} {B} nnAB nAB = nnAB (¬A→¬A×B nAB)

¬¬A×B→¬¬B : {A : Set ℓ} → {B : Set ℓ'} → ¬ ¬ (A × B) → ¬ ¬ B 
¬¬A×B→¬¬B {ℓ} {ℓ'} {A} {B} nnAB nAB = nnAB (¬B→¬A×B nAB)

A→B→A×B : {A : Set ℓ} → {B : Set ℓ'} → A → B → A × B
A→B→A×B a b = a , b

¬¬A→¬¬B→¬¬A×B : {A : Set ℓ} → {B : Set ℓ'} → ¬¬ A → ¬¬ B → ¬¬ (A × B)
¬¬A→¬¬B→¬¬A×B {ℓ}{ℓ'}{A}{B} nna nnb = λ z → nna (λ z₁ → nnb (λ z₂ → z (z₁ , z₂)))

¬A⊎¬B→¬A×B : {A : Set  ℓ} -> {B : Set  ℓ'} -> (¬ A) ⊎ (¬ B) ->  ¬ (A × B)  
¬A⊎¬B→¬A×B (inj₁ x) = λ w → x (proj₁ w)
¬A⊎¬B→¬A×B (inj₂ y) = λ w → y (proj₂ w)

A×B→¬'¬A⊎¬B : (A × B) -> ((¬ A) ⊎ (¬ B)) -> ⊥
A×B→¬'¬A⊎¬B (fst , snd) (inj₁ x) = x fst
A×B→¬'¬A⊎¬B (fst , snd) (inj₂ y) = y snd

¬¬A×¬¬B→¬'¬A⊎¬B : (¬¬ A) × (¬¬ B) -> ((¬ A) ⊎ (¬ B)) -> ⊥
¬¬A×¬¬B→¬'¬A⊎¬B {A = A} {B = B} x (inj₁ u) = A×B→¬'¬A⊎¬B x (inj₁ (A→¬¬A u))
¬¬A×¬¬B→¬'¬A⊎¬B {A = A} {B = B} x (inj₂ v) = A×B→¬'¬A⊎¬B x (inj₂ (A→¬¬A v))

¬¬A×B→¬'¬A⊎¬B : ¬¬ (A × B) -> ((¬ A) ⊎ (¬ B)) -> ⊥
¬¬A×B→¬'¬A⊎¬B nnab (inj₁ x) = ¬¬A×B→¬¬A nnab x
¬¬A×B→¬'¬A⊎¬B nnab (inj₂ y) = ¬¬A×B→¬¬B nnab y

¬'¬A×¬B→¬¬A×¬¬B : {A : Set  ℓ} -> {B : Set  ℓ'} -> ¬ ((¬ A) × (¬ B)) -> ¬¬ (A ⊎ B)
¬'¬A×¬B→¬¬A×¬¬B {ℓ} {ℓ'} {A} {B} nnab = converse ¬A⊎B→¬A×¬B  nnab

-- this proof was a little hard for some reason:
¬¬A→¬¬B'→¬¬A→B : {A : Set ℓ} → {B : Set ℓ'} → ((¬¬ A) → (¬¬ B)) → ¬¬ (A → B)
¬¬A→¬¬B'→¬¬A→B {ℓ}{ℓ'} {A}{B} x y =  A→¬¬A AB y
                           where
                            AnB : A → ¬ B
                            AnB = ¬A→B→A→¬B y
                            nnAnB : ¬¬ A → ¬ ¬ (¬ B)
                            nnAnB = A→B→¬¬A→¬¬B AnB
                            nnAnB' : ¬¬ A → ¬ B
                            nnAnB' nna = ¬¬¬A→¬A (nnAnB nna)
                            nnB : ¬¬ B → ¬ A
                            nnB nb = converse AnB nb
                            nA : ¬ A
                            nA a = nnB (x (A→¬¬A a)) a
                            AB : A → B
                            AB a = ⊥-elim (nA a)

¬¬A⟷¬¬B'→¬¬A⟷B : {A : Set ℓ} → {B : Set ℓ'} → ((¬¬ A) ⟷ (¬¬ B)) → ¬¬ (A ⟷ B)
¬¬A⟷¬¬B'→¬¬A⟷B {ℓ}{ℓ'} {A}{B} x = A→B→C→¬¬A→¬¬B→¬¬C (λ u v → record { AtoB = u ; BtoA = v })
  (¬¬A→¬¬B'→¬¬A→B (AtoB x)) (¬¬A→¬¬B'→¬¬A→B (BtoA x))

¬¬FALSE→⊥ : ¬¬ FALSE → ⊥
¬¬FALSE→⊥ nnf = ¬¬⊥→⊥ nnf


-------------------
-- NEW OPERATORS --
-------------------

-- Here are some more propositional operators, whose intended semantics are clear.
-- They are all isProp as is shown, and ¬¬-invariant. The ¬¬-invariance need not be
-- shown as it follows from the bijections that follow that identify upto logical
-- equivalence these operators and those defined in the classical logic proper
-- fragment. We thus have a clear idea of what classical propositional calculus
-- operators and propositions are in MLTT.

NOR : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ') 
NOR A B = (¬ A) × (¬ B)

isPropNOR : isProp (NOR A B)
isPropNOR = λ x y → refl

NOR2 : (A : Set  ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ') 
NOR2 A B = ¬ (A ⊎ B)

isPropNOR2 : isProp (NOR2 A B)
isPropNOR2 = λ x y → refl

OR : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ') 
OR A B = ¬ (NOR A B)

isPropOR : isProp (OR A B)
isPropOR = λ x y → refl

OR2 : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ') 
OR2 A B = ¬¬ (A ⊎ B)

isPropOR2 : isProp (OR2 A B)
isPropOR2 = λ x y → refl

AND : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ') 
AND A B = NOR (¬ A) (¬ B)

isPropAND : isProp (AND A B)
isPropAND = λ x y → refl

AND2 : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ') 
AND2 A B = ¬¬ (A × B)

isPropAND2 : isProp (AND2 A B)
isPropAND2 = λ x y → refl

NAND : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ') 
NAND A B = ¬ (AND A B)

isPropNAND : isProp (NAND A B)
isPropNAND = λ x y → refl

NAND2 : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ') 
NAND2 A B = ¬ (A × B)

isPropNAND2 : isProp (NAND2 A B)
isPropNAND2 = λ x y → refl

IMPLIES  : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ')
IMPLIES A B = NAND A (¬ B)

isPropIMPLIES : isProp (IMPLIES A B)
isPropIMPLIES = λ x y → refl

_⟺_ : (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ') 
A ⟺ B = ((A ⇒ B) × (B ⇒ A))

isProp⟺ : isProp (A ⟺ B)
isProp⟺ = λ x y → refl

BIJECTION : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ')
BIJECTION A B = OR (AND A B) (NOR A B)

isPropBIJECTION : isProp (BIJECTION A B)
isPropBIJECTION = λ x y → refl

BIJECTION2  : (A : Set  ℓ) -> (B : Set  ℓ') -> Set (ℓ ⊔ ℓ')
BIJECTION2 A B = ¬¬ ((A → B) × (B → A))

isPropBIJECTION2 : isProp (BIJECTION2 A B)
isPropBIJECTION2 = λ x y → refl

-- That these are all logically equivalent to their intended operators is now shown.
-- We thus have no concern about using them as classical operators. Further,
-- we know they all result in isProp terms when their arguments are applied. This
-- sort of procedure ensures the semantics of any proofs in classical logic remain
-- faithful to their intended meaning. 

-- We could continue with any number of such further constructions for any number
-- and any complexity of logical propositional operators.

-- We use Robbin "Mathematica Logic: A First Course", and the 'D' axioms therein,
-- as a guide.

-- Not that whilst constructive logical equivalence ⟷ is used here, when using
-- Cubical we shall proceed to using Cubical equality, which follows from
-- isomorphism, thus requiring the isProp property. Levels, in this section,
-- will cause no problem. In general we would want the levels of the Types on
-- both sides of ⟷ to be bumped up so that they are the same. This is because
-- of the nature of Cubical equality in Cubical Agda.

----------------------------------
-- PROOF OF CLASSICAL SEMANTICS --
----------------------------------

-- This includes what is effectively a library of lemmas.

-- We can start with that which is already proven, the classical semantics for NOT:
NOT'⟷NOT : ∀ {A : Set ℓ} → (NOT' A) ⟷ (NOT A)
NOT'⟷NOT {ℓ}{A} = sym⟷ D1

ORAB→NOTA→ISTRUEB : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → OR A B → NOT A → ISTRUE B
ORAB→NOTA→ISTRUEB {ℓ}{ℓ'}{A}{B} orab na = λ z → orab (na , z)

A⊎B→NOTA'→B : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → A ⊎ B → NOT A → B
A⊎B→NOTA'→B {ℓ} {ℓ'} {A} {B} (inj₁ x) nB = ⊥-elim (nB x)
A⊎B→NOTA'→B {ℓ} {ℓ'} {A} {B} (inj₂ y) nB = y

OR2AB→NOTA→ISTRUEB : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → OR2 A B → NOT A → ISTRUE B
OR2AB→NOTA→ISTRUEB {ℓ}{ℓ'}{A}{B} orab na = λ z → orab λ x → z (A⊎B→NOTA'→B x na)

OR'AB→NOTA→ISTRUEB : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → OR' A B → NOT A → ISTRUE B
OR'AB→NOTA→ISTRUEB {ℓ}{ℓ'}{A}{B} orab na = orab (λ z → z (λ z₁ z₂ → z₁ na))

OR'AB→NOTB→ISTRUEA : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → OR' A B → NOT B → ISTRUE A
OR'AB→NOTB→ISTRUEA {ℓ}{ℓ'}{A}{B} orab na = λ z → orab (λ z₁ → z₁ (λ z₂ z₃ → z₂ z)) na

NORAB→ORAB→⊥ : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → NOR A B → OR A B → ⊥
NORAB→ORAB→⊥ {ℓ} {ℓ'} {A} {B} (na , nb) orab = ORAB→NOTA→ISTRUEB orab na nb

NOR→OR→⊥ : NOR A B → (A ⊎ B) → ⊥
NOR→OR→⊥ norab (inj₁ x) = norab .proj₁ x
NOR→OR→⊥ norab (inj₂ y) = norab .proj₂ y

B→OR'AB : {A : Set ℓ} {B : Set ℓ'} → B → OR' A B
B→OR'AB {ℓ}{ℓ'}{A}{B} b x y = ⊥-elim (y b)

OR'AA→A : {A : Set  ℓ} → OR' A A → ¬¬ A
OR'AA→A {ℓ}{A} oraa = λ z → oraa (λ z₁ → z₁ (λ z₂ z₃ → z₂ z)) z

OR'AB→NORAB→FALSE : OR' A B → NOR A B → FALSE
OR'AB→NORAB→FALSE orab norab = orab (λ z → z (λ z₁ z₂ → z₁ (norab .proj₁))) (norab .proj₂)

NOTA→NOTB→NOT'A→NOT'B : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → (NOT A → NOT B) → NOT' A → NOT' B
NOTA→NOTB→NOT'A→NOT'B {ℓ}{ℓ'}{A}{B} nanb na = λ x y → x (nanb (D1R na))

A→¬NOT' : A → ¬ (NOT' A)
A→¬NOT' {ℓ}{A} a x = d1 x a 
             where
               d1 : NOT' A → NOT A
               d1 = BtoA D1

¬¬NOT'→NOT : ¬¬ (NOT' A) → NOT A
¬¬NOT'→NOT {ℓ}{A} nnnA x = nnnA (A→¬NOT' x)

nnA→n'n'A : NOT (NOT A) → NOT' (NOT' A)
nnA→n'n'A {ℓ}{A} nnA = λ x y → x (⊥-elim (nnA (¬¬NOT'→NOT x)))

nn'A→nA : NOT (NOT' A) → NOT (NOT A)
nn'A→nA nnA = λ z → nnA (λ z₁ z₂ → z₁ z)

nnA→nn'A : NOT (NOT A) → NOT (NOT' A)
nnA→nn'A {ℓ}{A} nnA = λ x → nnA (D1R x)

-- A (NOT A) Substitution lemma
A⟷B→NOTA⟷NOTB : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⟷ B) → (NOT A) ⟷ (NOT B)
A⟷B→NOTA⟷NOTB {ℓ} {ℓ'} {A} {B} record { AtoB = AtoB ; BtoA = BtoA } = record { AtoB = (λ z z₁ → z (BtoA z₁)) ;
                                                                                BtoA = (λ z z₁ → z (AtoB z₁)) }

A→OR'AB : {A : Set ℓ} {B : Set ℓ'} → A → OR' A B
A→OR'AB {ℓ}{ℓ'}{A}{B} a x y = x (A→¬NOT' a)

-- A (NOT' A)  Substitution lemma 
A⟷B→NOT'A⟷NOT'B : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⟷ B) → (NOT' A) ⟷ (NOT' B)
A⟷B→NOT'A⟷NOT'B {ℓ} {ℓ'} {A} {B} record { AtoB = AtoB ; BtoA = BtoA } =
  record { AtoB = NOTA→NOTB→NOT'A→NOT'B (λ z z₁ → z (BtoA z₁)) ;
           BtoA = NOTA→NOTB→NOT'A→NOT'B (λ z z₁ → z (AtoB z₁)) }

norAB→¬A : {A : Set  ℓ} → {B : Set  ℓ'} → NOT' (OR' A B) → ¬ A
norAB→¬A {ℓ}{ℓ'}{A}{B} norab x = step2 (A→¬¬A (λ ())) (λ w → w) 
                        where
                          step : OR' A B ⟷ TRUE 
                          step = record { AtoB = λ y → λ () ; BtoA = λ y → A→OR'AB x }
                          step1 : NOT' (OR' A B) ⟷ NOT' TRUE
                          step1 = A⟷B→NOT'A⟷NOT'B step 
                          step2 : NOT' TRUE
                          step2 = AtoB step1 norab

norAB→¬B : {A : Set  ℓ} → {B : Set  ℓ'} → NOT' (OR' A B) → ¬ B
norAB→¬B {ℓ}{ℓ'}{A}{B} norab x = step2 (A→¬¬A (λ ())) (λ w → w)
                        where
                          step : OR' A B ⟷ TRUE 
                          step = record { AtoB = λ y → λ () ; BtoA = λ y → λ z z₁ → z₁ x }
                          step1 : NOT' (OR' A B) ⟷ NOT' TRUE
                          step1 = A⟷B→NOT'A⟷NOT'B step
                          step2 : NOT' TRUE
                          step2 = AtoB step1 norab

-- NOR Semantics:
NOT'OR'⟷NOR : {A : Set  ℓ} → {B : Set  ℓ'} → NOT' (OR' A B) ⟷ NOR A B
NOT'OR'⟷NOR {ℓ}{ℓ'}{A}{B} = record { AtoB = λ x → norAB→¬A x , norAB→¬B x ;
                                      BtoA = λ x y → A→B→C→¬¬A→¬¬B→¬¬C OR'AB→NORAB→FALSE y (A→¬¬A x) }

-- NOR2 Semantics
NOT'OR'⟷NOR2  : {A : Set  ℓ} → {B : Set  ℓ'} → NOT' (OR' A B) ⟷ NOR2 A B
NOT'OR'⟷NOR2 {ℓ}{ℓ'}{A}{B} = record { AtoB = λ x → ¬A×¬B→¬A⊎B (AtoB NOT'OR'⟷NOR x) ;
                                       BtoA = λ x → BtoA NOT'OR'⟷NOR (¬A⊎B→¬A×¬B x) }

NOR⟷NOR2 : {A : Set  ℓ} -> {B : Set  ℓ'} -> NOR A B ⟷ NOR2 A B
NOR⟷NOR2 {ℓ}{ℓ'}{A}{B} = record { AtoB = λ x y → NOR→OR→⊥ x y ;
                                   BtoA = λ x → (λ z → x (inj₁ z)) , (λ z → x (inj₂ z)) }

-- OR Semantics (analogous to D2 in Robbin): 
D2 : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → (OR A B) ⟷ (OR' A B)
D2 {ℓ}{ℓ'}{A}{B} = record { AtoB = λ x y → ORAB→NOTA→ISTRUEB x ( ¬¬NOT'→NOT y) ;
                           BtoA = λ x y → NORAB→ORAB→⊥ y λ z → x (λ z₁ → z₁ (λ z₂ z₃ → z₂ (z .proj₁))) (y .proj₂)} 

OR'AB⟷ORAB : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → (OR' A B) ⟷ (OR A B)
OR'AB⟷ORAB = sym⟷ D2    

D2L : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → OR' A B → OR A B 
D2L {ℓ}{ℓ'}{A}{B} orab = λ z → orab (λ z₁ → z₁ (λ z₂ z₃ → z₂ (z .proj₁))) (z .proj₂)

D2R : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → OR A B → OR' A B
D2R {ℓ}{ℓ'}{A}{B} orab = AtoB D2 orab

OR'AB→NOT'A→ISTRUEAB : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → OR' A B → NOT' A → ISTRUE B
OR'AB→NOT'A→ISTRUEAB {ℓ}{ℓ'}{A}{B} orab na = ORAB→NOTA→ISTRUEB (D2L orab) (¬¬NOT'→NOT (A→¬¬A na))

OR'AB→NOTA→ISTRUEAB : {ℓ ℓ' : Level}{A : Set ℓ} {B : Set ℓ'} → OR' A B → NOT A → ISTRUE B
OR'AB→NOTA→ISTRUEAB {ℓ}{ℓ'}{A}{B} orab na = orab (λ z → z (λ z₁ z₂ → z₁ na))

OR'NOT'A'NOT'B-defHlp : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → OR' (NOT' A) (NOT' B) → OR' (NOT A) (NOT B)
OR'NOT'A'NOT'B-defHlp {ℓ}{ℓ'}{A}{B} ornot x y = OR'AB→NOTA→ISTRUEAB ornot (nnA→nn'A step) (nnA→nn'A y)
                               where
                                 step : NOT (NOT A)
                                 step = ¬¬NOT'→NOT x

OR'NOTA'NOTB-defHlp : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → OR' (NOT A) (NOT B) → OR' (NOT' A) (NOT' B)
OR'NOTA'NOTB-defHlp {ℓ}{ℓ'}{A}{B} ornot x = A→B→¬¬A→¬¬B D1L step2
                                 where
                                   step : NOT (NOT' A)
                                   step = ¬¬NOT'→NOT x
                                   step2 : ISTRUE (NOT B)
                                   step2 = OR'AB→NOTA→ISTRUEB {A = NOT A} ornot (nn'A→nA step) 

OR'NOT'A'NOT'B-def : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → OR' (NOT' A) (NOT' B) ⟷ OR' (NOT A) (NOT B)
OR'NOT'A'NOT'B-def {ℓ}{ℓ'}{A}{B} = record { AtoB = OR'NOT'A'NOT'B-defHlp ; BtoA = OR'NOTA'NOTB-defHlp } 

OR'NOTA'NOTB-def : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → OR' (NOT A) (NOT B) ⟷ OR (NOT A) (NOT B)
OR'NOTA'NOTB-def {ℓ}{ℓ'}{A}{B} = record { AtoB = λ ornot → D2L ornot ; BtoA = D2R }

OR'NOT'A'NOT'B-def2 : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → OR' (NOT' A) (NOT' B) ⟷  OR (NOT A) (NOT B)
OR'NOT'A'NOT'B-def2 {ℓ}{ℓ'}{A}{B} = trans⟷ OR'NOT'A'NOT'B-def OR'NOTA'NOTB-def 

-- an (OR A B) Substitution lemma
A⟷C→B⟷D→ORAB⟷ORCD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (OR A B) ⟷ (OR C D)
A⟷C→B⟷D→ORAB⟷ORCD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A} {B} {C}{D} record { AtoB = AtoC ; BtoA = CtoA }
  record { AtoB = BtoD ; BtoA = DtoB } = record { AtoB = λ x → λ z → x ((λ z₁ → z .proj₁ (AtoC z₁)) ,
    (λ z₁ → z .proj₂ (BtoD z₁))) ; BtoA = λ x → λ z → x ((λ z₁ → z .proj₁ (CtoA z₁)) , (λ z₁ → z .proj₂ (DtoB z₁))) }

-- swap A B
OR'AB→OR'BA : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (OR' A B) → (OR' B A)
OR'AB→OR'BA {ℓ}{ℓ'}{A}{B} orab = λ x → OR'AB→NOTB→ISTRUEA orab (¬¬NOT'→NOT x)

-- (OR' A B) Substitution lemma
A⟷C→OR'AB→OR'CB : {ℓ ℓ' ℓ'' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''} → (A ⟷ C) → (OR' A B) → (OR' C B)
A⟷C→OR'AB→OR'CB {ℓ} {ℓ'} {ℓ''} {A} {B} {C} record { AtoB = AtoC ; BtoA = CtoA } orab x y = OR'AB→NOTB→ISTRUEA orab y na 
                                                         where
                                                           nc : ¬ C
                                                           nc = ¬¬NOT'→NOT x
                                                           na : ¬ A
                                                           na = converse AtoC nc

-- (OR' A B) substitution lemma
A⟷C→B⟷D→OR'AB→OR'CB : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''} {D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (OR' A B) → (OR' C D)
A⟷C→B⟷D→OR'AB→OR'CB {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A} {B} {C} {D} AC BD orab =
  A⟷C→OR'AB→OR'CB AC (OR'AB→OR'BA (A⟷C→OR'AB→OR'CB BD (OR'AB→OR'BA orab)))

-- (OR' A B) substitution lemma
A⟷C→B⟷D→OR'AB⟷OR'CB : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}{D : Set ℓ'''} →
                        (A ⟷ C) → (B ⟷ D) → OR' A B ⟷ OR' C D
A⟷C→B⟷D→OR'AB⟷OR'CB AC BD = record { AtoB = A⟷C→B⟷D→OR'AB→OR'CB AC BD ;
  BtoA = A⟷C→B⟷D→OR'AB→OR'CB (record { AtoB = AC .BtoA ; BtoA = AC .AtoB }) (record { AtoB = BD .BtoA ; BtoA = BD .AtoB }) }


¬OR2⟷NOR2 : {A : Set ℓ} → {B : Set ℓ'} → (¬ (OR2 A B)) ⟷ (NOR2 A B)
¬OR2⟷NOR2 {ℓ}{ℓ'}{A}{B} = record { AtoB = λ z z₁ → z (λ z₂ → z₂ z₁) ; BtoA = λ z z₁ → z₁ z }

ORAB→OR2AB : {A : Set ℓ} → {B : Set ℓ'} → (OR A B) → (OR2 A B)
ORAB→OR2AB = λ z z₁ → z ((λ z₂ → z₁ (inj₁ z₂)) , (λ z₂ → z₁ (inj₂ z₂)))

OR2AB→ORAB : {A : Set ℓ} → {B : Set ℓ'} → (OR2 A B) → (OR A B)
OR2AB→ORAB {ℓ}{ℓ'}{A}{B} x = λ y → x (AtoB  NOT'OR'⟷NOR2 (step y))
               where
                 step : NOR A B → NOT' (OR' A B)
                 step = BtoA NOT'OR'⟷NOR 

-- Semantics of OR2, analogous to D2 of Robbins:
D2' : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → (OR' A B) ⟷ (OR2 A B)
D2' {ℓ}{ℓ'}{A}{B} = trans⟷ OR'AB⟷ORAB (record { AtoB = ORAB→OR2AB ; BtoA = OR2AB→ORAB })

OR'AB⟷OR2AB = D2'

nnA×nnB→¬OR¬A¬B : ¬ (OR (¬ A) (¬ B)) → (¬¬ A) × (¬¬ B)
nnA×nnB→¬OR¬A¬B nonanb = (λ z → nonanb (λ z₁ → z₁ .proj₁ z)) , (λ z → nonanb (λ z₁ → z₁ .proj₂ z))

¬⊎→¬OR' : {A : Set ℓ}{B : Set ℓ'} → ¬ (A ⊎ B) → ¬ (OR' A B)
¬⊎→¬OR' {ℓ}{ℓ'}{A}{B} nab  = λ z → z (λ z₁ → z₁ (λ z₂ z₃ → z₂ (λ z₄ → nab (inj₁ z₄)))) (λ z₁ → nab (inj₂ z₁))

¬¬OR'→¬¬⊎ : {A : Set ℓ}{B : Set ℓ'} → ¬¬ (OR' A B) → ¬¬ (A ⊎ B)
¬¬OR'→¬¬⊎ {ℓ}{ℓ'}{A}{B} nnorab = converse ¬⊎→¬OR' nnorab 

OR'→¬¬⊎ : {A : Set ℓ}{B : Set ℓ'} → (OR' A B) → ¬¬ (A ⊎ B)
OR'→¬¬⊎ {ℓ}{ℓ'}{A}{B} orab = λ z → orab (λ z₁ → z₁ (λ z₂ z₃ → z₂ (λ z₄ → z (inj₁ z₄)))) (λ z₁ → z (inj₂ z₁))

¬¬⊎→OR' : {A : Set ℓ}{B : Set ℓ'} → ¬¬ (A ⊎ B) → OR' A B
¬¬⊎→OR' {ℓ}{ℓ'}{A}{B} nnab x y = A→B→C→¬¬A→¬¬B→¬¬C A⊎B→NOTA'→B nnab (A→B→¬¬A→¬¬B D1R x) y

ANDAB-def : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → AND A B ⟷ NOT (OR (NOT A) (NOT B))
ANDAB-def {ℓ} {ℓ'} {A} {B} = record { AtoB = λ z z₁ → z₁ z ; BtoA = λ x → nnA×nnB→¬OR¬A¬B x }

AND'AB-def : {ℓ ℓ' : Level} {A : Set ℓ}{B : Set ℓ'} → AND' A B ⟷ NOT (OR (NOT A) (NOT B))
AND'AB-def {ℓ} {ℓ'} {A} {B} = trans⟷ (sym⟷ D1) step
                            where
                              step : NOT (OR' (NOT' A) (NOT' B)) ⟷ NOT (OR (NOT A) (NOT B))
                              step = A⟷B→NOTA⟷NOTB (OR'NOT'A'NOT'B-def2 {A = A}{B = B}) 

-- Another OR' equivalent semantics:
¬¬A⊎B⟷OR' : {A : Set ℓ}{B : Set ℓ'} → (¬¬ (A ⊎ B)) ⟷ (OR' A B)
¬¬A⊎B⟷OR' {ℓ}{ℓ'}{A}{B} = record { AtoB = ¬¬⊎→OR' ; BtoA = OR'→¬¬⊎ }

-- Semantics of AND, Analogous to D3 of Robbins :
D3 : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND A B ⟷ AND' A B
D3 {ℓ}{ℓ'}{A}{B} = trans⟷ ANDAB-def (sym⟷ (AND'AB-def {A = A}{B = B}))

-- Semantics of AND
AND'AB⟷ANDAB : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND' A B ⟷ AND A B
AND'AB⟷ANDAB = sym⟷ D3 

D3R : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND A B → AND' A B
D3R {ℓ}{ℓ'}{A}{B} andab = AtoB D3 andab 

A×B→AND : {A : Set  ℓ} → {B : Set  ℓ'} → (A × B) → AND A B
A×B→AND {ℓ} {ℓ'} {A} {B} A×B = (λ z → z (A×B .proj₁)) , (λ z → z (A×B .proj₂))

AND₁ : AND A B -> ISTRUE A
AND₁ (fst , snd) =  fst

AND₂ : AND A B -> ISTRUE B
AND₂ (fst , snd) = snd

¬¬A→¬¬B→ANDAB : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → ¬¬ A → ¬¬ B → AND A B
¬¬A→¬¬B→ANDAB {ℓ} {ℓ'} {A} {B} nnA nnB = nnA , nnB

¬¬A→¬¬B→AND'AB : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → ¬¬ A → ¬¬ B → AND' A B
¬¬A→¬¬B→AND'AB {ℓ} {ℓ'} {A} {B} nnA nnB = D3 .AtoB (¬¬A→¬¬B→ANDAB nnA nnB)

AND'AB→ISTRUEA  : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND' A B → ISTRUE A
AND'AB→ISTRUEA  {ℓ}{ℓ'}{A}{B} andab = proj₁ (nnA×nnB→¬OR¬A¬B {A = A}{B = B} step)
                              where
                                step : NOT (OR (NOT A) (NOT B))
                                step = AtoB AND'AB-def andab

AND'AB→ISTRUEB  : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND' A B → ISTRUE B
AND'AB→ISTRUEB  {ℓ}{ℓ'}{A}{B} andab = proj₂ (nnA×nnB→¬OR¬A¬B {A = A}{B = B} step)
                              where
                                step : NOT (OR (NOT A) (NOT B))
                                step = AtoB AND'AB-def andab
                                  
-- swap A B
symAND' :  {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → AND' A B → AND' B A
symAND' {ℓ}{ℓ'} {A}{B} AB = ¬¬A→¬¬B→AND'AB (AND'AB→ISTRUEB AB) (AND'AB→ISTRUEA AB)

-- AND A B  Substitution lemma
A⟷C→B⟷D→ANDAB→ANDCD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (AND A B) → (AND C D)
A⟷C→B⟷D→ANDAB→ANDCD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A}{B}{C}{D} = λ z z₁ z₂ →
                                                            (λ z₃ → z₂ .proj₁ (λ z₄ → z₃ (z .AtoB z₄))) ,
                                                            (λ z₃ → z₂ .proj₂ (λ z₄ → z₃ (z₁ .AtoB z₄)))

-- AND A B  Substitution lemma
A⟷C→B⟷D→ANDAB⟷ANDCD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (AND A B) ⟷ (AND C D)
A⟷C→B⟷D→ANDAB⟷ANDCD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A}{B}{C}{D} AC BD =
  record { AtoB = A⟷C→B⟷D→ANDAB→ANDCD AC BD ;
           BtoA = A⟷C→B⟷D→ANDAB→ANDCD (sym⟷ AC) (sym⟷ BD) }

-- AND' A B  Substitution lemma
A⟷C→B⟷D→AND'AB→AND'CD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (AND' A B) → (AND' C D)
A⟷C→B⟷D→AND'AB→AND'CD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A}{B}{C}{D} AC BD andab = D3 .AtoB step
                                              where
                                                step : AND C D
                                                step = A⟷C→B⟷D→ANDAB→ANDCD AC BD (D3 .BtoA andab)

-- AND' A B  Substitution lemma
A⟷C→B⟷D→AND'AB⟷AND'CD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}{D : Set ℓ'''} →
                          (A ⟷ C) → (B ⟷ D) → AND' A B ⟷ AND' C D
A⟷C→B⟷D→AND'AB⟷AND'CD AC BD =
  record { AtoB = A⟷C→B⟷D→AND'AB→AND'CD AC BD ;
           BtoA = A⟷C→B⟷D→AND'AB→AND'CD (record { AtoB = AC .BtoA ; BtoA = AC .AtoB })
             (record { AtoB = BD .BtoA ; BtoA = BD .AtoB }) }

-- Semantics of AND2, Analogous to D3 of Robbins :
D3' : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND2 A B ⟷ AND' A B
D3' {ℓ}{ℓ'}{A}{B} = trans⟷ (record { AtoB = λ z → (λ z₁ → z (λ z₂ → z₁ (z₂ .proj₁))) ,
                                   (λ z₁ → z (λ z₂ → z₁ (z₂ .proj₂))) ;
                                   BtoA = λ z z₁ → z .proj₁ (λ z₂ → z .proj₂ (λ z₃ → z₁ (z₂ , z₃))) })  D3

-- Semantics of AND2
AND'AB⟷AND2AB : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND' A B ⟷ AND2 A B
AND'AB⟷AND2AB = sym⟷ D3'

-- Also we can do this:
AND⟷AND2 : {ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → AND A B ⟷ AND2 A B
AND⟷AND2 {ℓ}{ℓ'}{A}{B} = record { AtoB = λ z z₁ → z .proj₁ (λ z₂ → z .proj₂ (λ z₃ → z₁ (z₂ , z₃))) ;
                                 BtoA = λ z → (λ z₁ → z (λ z₂ → z₁ (z₂ .proj₁))) , (λ z₁ → z (λ z₂ → z₁ (z₂ .proj₂))) }

NAND⟷NOT'AND'Hlp : {A : Set  ℓ} → {B : Set  ℓ'} → NOT' (AND' A B) ⟷ (¬ (AND2 A B))
NAND⟷NOT'AND'Hlp {ℓ}{ℓ'}{A}{B} = trans⟷ step NOT'⟷NOT
               where
                 step : NOT' (AND' A B) ⟷ NOT' (AND2 A B) 
                 step = A⟷B→NOT'A⟷NOT'B {A = AND' A B} AND'AB⟷AND2AB

NAND⟷NOT'AND'Hlp2 : {A : Set  ℓ} → {B : Set  ℓ'} → (¬ (A × B)) ⟷ (¬ (AND2 A B))
NAND⟷NOT'AND'Hlp2 {ℓ}{ℓ'}{A}{B} = record { AtoB = λ z z₁ → z₁ z ; BtoA = λ z z₁ → z (λ z₂ → z₂ z₁) }

-- So, NAND and NAND2 are both the classical Nand:
NAND⟷NOT'AND' : {A : Set  ℓ} → {B : Set  ℓ'} → (NAND2 A B) ⟷ (NOT' (AND' A B))
NAND⟷NOT'AND' {ℓ}{ℓ'}{A}{B} = trans⟷ NAND⟷NOT'AND'Hlp2 (sym⟷ NAND⟷NOT'AND'Hlp)

NAND⟷NAND2 : {A : Set  ℓ} → {B : Set  ℓ'} → (NAND A B) ⟷ (NAND2 A B)
NAND⟷NAND2 {ℓ}{ℓ'}{A}{B} = record { AtoB = λ x → λ z → x ((λ z₁ → z₁ (z .proj₁)) , (λ z₁ → z₁ (z .proj₂))) ;
                                   BtoA = λ x → λ z → z .proj₁ (λ z₁ → z .proj₂ (λ z₂ → x (z₁ , z₂))) }

-- Classical semantics for IMPLIES:
IMPLIES⟷A⇒B : {A : Set  ℓ} → {B : Set  ℓ'} → (IMPLIES A B) ⟷ (A ⇒ B)
IMPLIES⟷A⇒B {ℓ}{ℓ'}{A}{B} = record { AtoB = λ z z₁ z₂ → z₁ (λ z₃ → z ((λ z₄ → z₄ z₃) , (λ z₄ → z₄ z₂))) ;
                                    BtoA = λ z z₁ →
                                              z₁ .proj₁
                                              (λ z₂ → z (λ z₃ → z₃ z₂) (λ z₃ → z₁ .proj₂ (λ z₄ → z₄ z₃))) }

A⇒B→¬¬'A→B : {A : Set ℓ} → {B : Set ℓ'} → (A ⇒ B) → ¬¬ (A → B)
A⇒B→¬¬'A→B {ℓ}{ℓ'}{A}{B} ab = ¬¬A→¬¬B'→¬¬A→B ab

¬¬A→¬¬B→A⇒B : {A : Set ℓ} → {B : Set ℓ'} → ((¬¬ A) → (¬¬ B)) → A ⇒ B
¬¬A→¬¬B→A⇒B {ℓ}{ℓ'}{A}{B} nnA nnB = nnA nnB

⇒trans : {A : Set ℓ} -> {B : Set ℓ'} -> {C : Set ℓ''} -> (A ⇒ B) -> (B ⇒ C) -> (A ⇒ C)
⇒trans {ℓ} {ℓ'} {ℓ''} {A} {B} {C} AB BC x = BC (AB x)

A⟷B→A⟺B : {A : Set ℓ} → {B : Set ℓ'} → (A ⟷ B) → (A ⟺ B)
A⟷B→A⟺B {ℓ} {ℓ'} {A} {B} record { AtoB = AtoB ; BtoA = BtoA } =
  ¬¬A→¬¬B→A⇒B (¬¬A→B'→¬¬A→¬¬B (A→¬¬A AtoB)) , ¬¬A→¬¬B→A⇒B (¬¬A→B'→¬¬A→¬¬B (A→¬¬A BtoA))

¬¬A⟷¬¬B→A⟺B : {A : Set ℓ} -> {B : Set ℓ'} -> (¬¬ A) ⟷ (¬¬ B) -> A ⟺ B 
¬¬A⟷¬¬B→A⟺B {A = A} {B = B} record { AtoB = AtoB ; BtoA = BtoA } = AtoB , BtoA

A⟺B→¬¬A⟷¬¬B : {A : Set ℓ} -> {B : Set ℓ'} -> A ⟺ B -> (¬¬ A) ⟷ (¬¬ B) 
A⟺B→¬¬A⟷¬¬B {A = A} {B = B} (fst , snd) = record { AtoB = fst ; BtoA = snd }

A⟺B⟷¬¬A⟷B : {A : Set ℓ} -> {B : Set ℓ'} -> (A ⟺ B) ⟷ (¬¬ (A ⟷ B))
A⟺B⟷¬¬A⟷B {ℓ}{ℓ'}{A}{B} = record { AtoB = λ ab → ¬¬A⟷¬¬B'→¬¬A⟷B (A⟺B→¬¬A⟷¬¬B ab) ;
                                     BtoA = λ nnab → ¬¬A⟷¬¬B→A⟺B (¬¬A⟷B¬¬A⟷¬¬B nnab) }

⇒idem : {A : Set ℓ} → A ⇒ A
⇒idem {A = A} a b = a b

⟺refl :  {A : Set ℓ} -> (A ⟺ A) 
⟺refl {A = A} = ⇒idem , ⇒idem 

⟺sym :  {A : Set ℓ} -> {B : Set ℓ'} -> (A ⟺ B) → (B ⟺ A)
⟺sym {A = A} {B = B} (fst , snd) = snd , fst

⟺fst : {A : Set ℓ} -> {B : Set ℓ'} → A ⟺ B → (A ⇒ B)
⟺fst {A = A} {B = B} (fst , snd) = fst

⟺snd : {A : Set ℓ} -> {B : Set ℓ'} → A ⟺ B → (B ⇒ A)
⟺snd {A = A} {B = B} (fst , snd) = snd

⟺trans : {A : Set ℓ} -> {B : Set ℓ'} -> {C : Set ℓ'} -> (A ⟺ B) → (B ⟺ C) → (A ⟺ C)
⟺trans {ℓ} {ℓ'} {A} {B} {C} (fst , snd) (fst' , snd') = ⇒trans fst fst' , ⇒trans snd' snd

¬¬InvariantA⟺B : {A : Set ℓ} -> {B : Set ℓ'} -> ¬¬ (A ⟺ B) → A ⟺ B
¬¬InvariantA⟺B {ℓ}{ℓ'}{A}{B} nnab = ¬¬Invariant⇒ (A→B→¬¬A→¬¬B ⟺fst nnab) , ¬¬Invariant⇒ (A→B→¬¬A→¬¬B ⟺snd nnab)

-- A ⇒ B  Substitution lemma
A⟷C→B⟷D→A⇒B→C⇒D : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (A ⇒ B) → (C ⇒ D)
A⟷C→B⟷D→A⇒B→C⇒D AC BD AB = λ z z₁ →
                              z (λ z₂ → AB (λ z₃ → z₃ (AC .BtoA z₂)) (λ z₃ → z₁ (BD .AtoB z₃)))

A⟷C→B⟷D→A⇒B⟷C⇒D : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {D : Set ℓ'''} →
                   (A ⟷ C) → (B ⟷ D) → (A ⇒ B) ⟷ (C ⇒ D)
A⟷C→B⟷D→A⇒B⟷C⇒D AC BD .AtoB = A⟷C→B⟷D→A⇒B→C⇒D AC BD
A⟷C→B⟷D→A⇒B⟷C⇒D AC BD .BtoA = A⟷C→B⟷D→A⇒B→C⇒D
  (record { AtoB = AC .BtoA ; BtoA = AC .AtoB }) (record { AtoB = BD .BtoA ; BtoA = BD .AtoB })

A⇔B→AND'A⇒B'B⇒A' : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → A ⇔ B → AND (A ⇒ B) (B ⇒ A) 
A⇔B→AND'A⇒B'B⇒A' {ℓ}{ℓ'}{A}{B} AB = step AB
                           where
                             step : AND' (A ⇒ B) (B ⇒ A) → AND (A ⇒ B) (B ⇒ A)
                             step = D3 {A = A ⇒ B} {B = B ⇒ A} .BtoA

A⇔B→A⇒B : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⇔ B) → (A ⇒ B)
A⇔B→A⇒B {ℓ}{ℓ'} {A}{B} AB = ¬¬'¬¬A→¬¬B (AND₁ (A⇔B→AND'A⇒B'B⇒A' AB))

--  A ⇔ B  Substitution lemma
A⟷C→B⟷D→A⇔B→C⇔D : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (A ⇔ B) → (C ⇔ D)
A⟷C→B⟷D→A⇔B→C⇔D {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD AB =
  A⟷C→B⟷D→AND'AB→AND'CD
    (record { AtoB = step ;
              BtoA = A⟷C→B⟷D→A⇒B→C⇒D
    (record { AtoB = AC .BtoA ; BtoA = AC .AtoB })
    (record { AtoB = BD .BtoA ;
              BtoA = BD .AtoB }) })
    (record { AtoB = A⟷C→B⟷D→A⇒B→C⇒D BD AC ;
              BtoA = A⟷C→B⟷D→A⇒B→C⇒D
    (record { AtoB = BtoA BD ; BtoA = AtoB BD })
    (record { AtoB = BtoA AC ; BtoA = AtoB AC }) })
       AB
         where
           step : A ⇒ B → C ⇒ D
           step = A⟷C→B⟷D→A⇒B→C⇒D AC BD

-- A ⇔ B Substitution lemma
A⟷C→B⟷D→A⇔B⟷C⇔D :  {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (A ⇔ B) ⟷ (C ⇔ D)
A⟷C→B⟷D→A⇔B⟷C⇔D {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD = record { AtoB = A⟷C→B⟷D→A⇔B→C⇔D AC BD ; BtoA = cdab }
  where
    cdab : (C ⇔ D) → (A ⇔ B)
    cdab = A⟷C→B⟷D→A⇔B→C⇔D {A = C}{B = D}{C = A}{D = B} (record { AtoB = AC .BtoA ; BtoA = AC .AtoB })
      (record { AtoB = BD .BtoA ; BtoA = BD .AtoB }) 

sym⇔ : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → A ⇔ B → B ⇔ A
sym⇔ {ℓ}{ℓ'}{A}{B} AB = step2 (¬¬A→¬¬B→ANDAB step4 step3)
                   where
                     step : AND' (A ⇒ B) (B ⇒ A) → AND (A ⇒ B) (B ⇒ A)
                     step = D3 {A = A ⇒ B} {B = B ⇒ A} .BtoA
                     step2 : AND (B ⇒ A) (A ⇒ B) → AND' (B ⇒ A) (A ⇒ B)
                     step2 = D3 {A = (B ⇒ A)} {B = A ⇒ B} .AtoB  
                     step3 = AND₁ (step AB)
                     step4 = AND₂ (step AB)

-- Classical semantics of _⟺_, analogous to D4:
A⇔B⟷A⟺B : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⇔ B) ⟷ (A ⟺ B)
A⇔B⟷A⟺B {ℓ}{ℓ'} {A}{B} = record { AtoB = λ x → A⇔B→A⇒B x , A⇔B→A⇒B (sym⇔ x) ;
                                    BtoA = λ x → D3 {A = A ⇒ B} {B = B ⇒ A} .AtoB (step x) }
                   where
                     step : (A ⟺ B) → AND (A ⇒ B) (B ⇒ A)
                     step AB = ¬¬A→¬¬B→ANDAB (A→¬¬A (⟺fst AB)) (A→¬¬A (⟺snd AB))

-- A ⟺ B Substitution lemma
A⟷C→B⟷D→A⟺B⟷C⟺D :  {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟷ C) → (B ⟷ D) → (A ⟺ B) ⟷ (C ⟺ D)
A⟷C→B⟷D→A⟺B⟷C⟺D {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD =
  trans⟷ (sym⟷ A⇔B⟷A⟺B) (trans⟷ (A⟷C→B⟷D→A⇔B⟷C⇔D AC BD) A⇔B⟷A⟺B)

A⇔B→A⟺B : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⇔ B) → (A ⟺ B)
A⇔B→A⟺B {ℓ}{ℓ'} {A}{B} = AtoB A⇔B⟷A⟺B

A⟺B→A⇔B : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⟺ B) → (A ⇔ B)
A⟺B→A⇔B {ℓ}{ℓ'} {A}{B} = BtoA  A⇔B⟷A⟺B

A⟷B→A⟺B' : {A : Set ℓ} → {B : Set ℓ'} → (A ⟷ B) → (A ⟺ B)
A⟷B→A⟺B' = A⟷B→A⟺B

A⟺B⟷A⇔B : {A : Set ℓ} → {B : Set ℓ'} → (A ⟺ B) ⟷ (A ⇔ B)
A⟺B⟷A⇔B = sym⟷ A⇔B⟷A⟺B

BIJECTION2-def : {A : Set  ℓ} -> {B : Set  ℓ'} → BIJECTION2 A B →  ¬¬ ((A → B) × (B → A))
BIJECTION2-def {ℓ}{ℓ'}{A}{B} bab = bab

A⟺B→BIJECTION2 : {A : Set  ℓ} → {B : Set  ℓ'} → A ⟺ B → BIJECTION2 A B  
A⟺B→BIJECTION2 {ℓ}{ℓ'}{A}{B} (ab , ba) x = ¬¬×-def (A⇒B→¬¬'A→B ab) (A⇒B→¬¬'A→B ba) x

BIJECTION→A⟺B : {A : Set  ℓ} → {B : Set  ℓ'} → (BIJECTION A B) → (A ⟺ B)
BIJECTION→A⟺B {ℓ}{ℓ'}{A}{B} ab = (λ z z₁ → ab ((λ z₂ → z₂ .proj₂ z₁) , (λ z₂ → z (z₂ .proj₁)))) ,
                                (λ z z₁ → z (λ z₂ → ab ((λ z₃ → z₃ .proj₁ z₁) , (λ z₃ → z₃ .proj₂ z₂))))

BIJECTION2→A⟺B : {A : Set  ℓ} → {B : Set  ℓ'} → BIJECTION2 A B → A ⟺ B
BIJECTION2→A⟺B {ℓ}{ℓ'}{A}{B} ab = (¬¬A→B'→¬¬A→¬¬B AB) , (¬¬A→B'→¬¬A→¬¬B BA)
                                 where
                                   AB : ¬¬ (A → B)
                                   AB = (¬¬fst (BIJECTION2-def ab))
                                   BA : ¬¬ (B → A)
                                   BA = ¬¬snd (BIJECTION2-def ab)

A→NOT'A→⊥ : {A : Set  ℓ} → A → NOT' A → ⊥
A→NOT'A→⊥ {ℓ} {A} a na = na (λ z → z a) λ ()

A→NOT'A⟷⊥ : {A : Set  ℓ} → A → (NOT' A) ⟷ ⊥
A→NOT'A⟷⊥ {ℓ}{A} a = record { AtoB = A→NOT'A→⊥ a ; BtoA = ⊥-elim }

A→B→OR'NOT'ANOT'B : {A : Set  ℓ} → {B : Set  ℓ'} → A → B → OR' (NOT' A) (NOT' B) → ⊥  
A→B→OR'NOT'ANOT'B {ℓ}{ℓ'}{A}{B} a b ornanb = OR'AA→A obabb λ ()
                             where
                               obabb : OR' ⊥ ⊥ 
                               obabb = A⟷C→B⟷D→OR'AB→OR'CB (A→NOT'A⟷⊥ a) (A→NOT'A⟷⊥ b) ornanb

A⟺B→BIJECTION-Hlp : {A : Set  ℓ} → {B : Set  ℓ'} → OR' (AND' A B) (NOT' (OR' A B)) →  OR (AND A B) (NOR A B)
A⟺B→BIJECTION-Hlp {ℓ}{ℓ'}{A}{B} oanor = D2L (A⟷C→B⟷D→OR'AB→OR'CB (sym⟷ D3) NOT'OR'⟷NOR oanor)

AND'-def : {A : Set ℓ}{B : Set ℓ'} → A → B → AND' A B
AND'-def {ℓ}{ℓ'}{A}{B} a b x = λ y → ¬¬FALSE→⊥ (A→B→¬¬A→¬¬B (A→B→OR'NOT'ANOT'B a b) x)

nnX : {X : Set ℓ} → ¬ (X ⇒ ⊥) → ¬¬ X
nnX {ℓ}{X} nX = λ z → nX (λ z₁ z₂ → z₁ z)

⇒→¬ : {X : Set ℓ} → X ⇒ ⊥ → ¬ X
⇒→¬ {ℓ}{X} nx = λ x → nx (A→¬¬A x) (λ ())

nnY-Hlp : {Y : Set ℓ} → (¬ Y) ⇒ ⊥ → ¬ (Y ⇒ ⊥)
nnY-Hlp {ℓ}{Y} ny = λ x → ⇒→¬ ny (⇒→¬ x)

nnY : {Y : Set ℓ} → ¬¬ (Y ⇒ ⊥) → ¬ ((¬ Y) ⇒ ⊥)
nnY {ℓ}{Y} ny x = ny (nnY-Hlp x)

converse' : {X : Set ℓ} {Y : Set ℓ'} → (X ⇒ Y) → ((Y ⇒ ⊥) ⇒ (X ⇒ ⊥))
converse' {ℓ}{ℓ'}{X}{Y} xy = λ x y → converse xy (nnX (nnY x)) (nnX y)

A→B×B→A'→A⊎B→A×B : {A : Set  ℓ} → {B : Set  ℓ'} → ((A → B) × (B → A)) → (A ⊎ B) → (A × B)
A→B×B→A'→A⊎B→A×B {ℓ} {ℓ'} {A} {B} (ab , ba) (inj₁ x) = x , ab x
A→B×B→A'→A⊎B→A×B {ℓ} {ℓ'} {A} {B} (ab , ba) (inj₂ y) = ba y , y

A⇔B→ORANDNOR-Hlp3 : {A : Set  ℓ} → {B : Set  ℓ'} → ¬¬ ((A → B) × (B → A)) → ¬¬ (A ⊎ B) → ¬¬ (A × B)
A⇔B→ORANDNOR-Hlp3 {ℓ} {ℓ'} {A} {B} ab aorb = A→B→C→¬¬A→¬¬B→¬¬C A→B×B→A'→A⊎B→A×B ab aorb

A⇔B→ORANDNOR-Hlp : {A : Set  ℓ} → {B : Set  ℓ'} → AND' (A ⇒ B) (B ⇒ A) → ¬¬ (OR' A B) → ¬¬ (AND' A B)
A⇔B→ORANDNOR-Hlp {ℓ}{ℓ'}{A}{B} ab' nnorab = A→B→¬¬A→¬¬B (λ x -> D3R (A×B→AND x))  nna×b
                          where
                           ab : ¬¬ (A → B)
                           ab = ¬¬A→¬¬B'→¬¬A→B (¬¬'¬¬A→¬¬B (AND'AB→ISTRUEA ab'))
                           ba : ¬¬ (B → A)
                           ba = ¬¬A→¬¬B'→¬¬A→B (¬¬'¬¬A→¬¬B (AND'AB→ISTRUEB ab'))
                           nnab : ¬¬ ((A → B) × (B → A))
                           nnab = ¬¬A→¬¬B→¬¬A×B ab ba
                           nna×b : ¬¬ (A × B) 
                           nna×b = A⇔B→ORANDNOR-Hlp3 nnab (¬¬OR'→¬¬⊎ nnorab) 

A⇔B→ORANDNOR : {A : Set  ℓ} → {B : Set  ℓ'} → AND' (A ⇒ B) (B ⇒ A) → ((AND' A B) ⇒ ⊥) ⇒ ((OR' A B) ⇒ ⊥)
A⇔B→ORANDNOR {ℓ}{ℓ'}{A}{B} ab' = converse' (A⇔B→ORANDNOR-Hlp ab')
                      
A⟺B→BIJECTION : {A : Set  ℓ} → {B : Set  ℓ'} → (A ⟺ B) → BIJECTION A B
A⟺B→BIJECTION {ℓ} {ℓ'} {A} {B} (ab , ba) = A⟺B→BIJECTION-Hlp (A⇔B→ORANDNOR a⇔b)
                                       where
                                         a⇔b : A ⇔ B
                                         a⇔b = AND'-def ab ba 

-- Classical semantics for BIJECTION (via _⟺_):
⟺⟷BIJECTION : {A : Set  ℓ} → {B : Set  ℓ'} → (A ⟺ B) ⟷ BIJECTION A B
⟺⟷BIJECTION {ℓ}{ℓ'}{A}{B} = record { AtoB = A⟺B→BIJECTION ; BtoA = BIJECTION→A⟺B }

-- Classical semantics for BIJECTION2 variants:
⟺⟷BIJECTION2 : {A : Set  ℓ} → {B : Set  ℓ'} → (A ⟺ B) ⟷ BIJECTION2 A B
⟺⟷BIJECTION2 {ℓ}{ℓ'}{A}{B} = record { AtoB = A⟺B→BIJECTION2 ; BtoA = BIJECTION2→A⟺B }

-- More semantics for bijection variants:
BIJECTION⟷BIJECTION2 : {A : Set  ℓ} → {B : Set  ℓ'} → BIJECTION A B ⟷ BIJECTION2 A B
BIJECTION⟷BIJECTION2  {ℓ}{ℓ'}{A}{B} = record { AtoB = λ x y → A⟺B→BIJECTION2 (BIJECTION→A⟺B x) y ;
                                              BtoA = λ x → AtoB ⟺⟷BIJECTION (BIJECTION2→A⟺B x) }

BIJECTION⟷⟺ : {A : Set  ℓ} → {B : Set  ℓ'} → (BIJECTION A B) ⟷ (A ⟺ B) 
BIJECTION⟷⟺ {ℓ}{ℓ'}{A}{B} = sym⟷ ⟺⟷BIJECTION

-- And now a Substitution lemma for _⟺_ shows it is also a (classical) logical equality.
-- Classical because of A⇔B⟷A⟺B, above. Though the substiotution lemma SUBST⟺-lemma is not
-- itself classical.

SUBST⟺-Hlp : (OP : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> (OP' : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> ({ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → (OP A B) ⟺ (OP' A B))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⟷ C) → (B ⟷ D) → ((OP A B) ⟺ (OP C D)))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⟷ C) → (B ⟷ D) → ((OP' A B) ⟺ (OP' C D)))
SUBST⟺-Hlp OP OP' OP⟷OP' substOP {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD =
  ¬¬A⟷¬¬B→A⟺B (SUBST⟷-lemma (λ A₁ B₁ → ¬¬ (OP A₁ B₁)) (λ A₁ B₁ → ¬¬ (OP' A₁ B₁))
   (A⟺B→¬¬A⟷¬¬B OP⟷OP')
   (λ ac bd → A⟺B→¬¬A⟷¬¬B (substOP ac bd)) AC BD)

SUBST⟺-lemma : (OP : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> (OP' : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> ({ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → (OP A B) ⟺ (OP' A B))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⟺ C) → (B ⟺ D) → ((OP A B) ⟺ (OP C D)))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⟺ C) → (B ⟺ D) → ((OP' A B) ⟺ (OP' C D)))
SUBST⟺-lemma OP OP' OP⟷OP' substOP {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD = ¬¬InvariantA⟺B (step2 nnAC nnBD)
  where
    nnBD : ¬¬ (B ⟷ D)
    nnBD = ¬¬A⟷¬¬B'→¬¬A⟷B (A⟺B→¬¬A⟷¬¬B BD)
    nnAC : ¬¬ (A ⟷ C)
    nnAC = ¬¬A⟷¬¬B'→¬¬A⟷B (A⟺B→¬¬A⟷¬¬B AC)
    step1 : (A ⟷ C) → (B ⟷ D) → ((OP' A B) ⟺ (OP' C D))
    step1 = SUBST⟺-Hlp OP OP' OP⟷OP' λ u v → substOP (A⟷B→A⟺B u) (A⟷B→A⟺B v)
    step2 : ¬¬ (A ⟷ C) → ¬¬ (B ⟷ D) → ¬¬ ((OP' A B) ⟺ (OP' C D))
    step2 = A→B→C→¬¬A→¬¬B→¬¬C step1
                                        
-- We can make this classicality clearer by showing this in terms of _⇔_
-- We will, however, prefer to use the simpler _⟺_ where possible.

SUBST⇔-lemma : (OP : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> (OP' : {ℓ ℓ' : Level} -> (A : Set ℓ) -> (B : Set ℓ') -> Set (ℓ ⊔ ℓ'))
            -> ({ℓ ℓ' : Level} → {A : Set ℓ} → {B : Set ℓ'} → (OP A B) ⇔ (OP' A B))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⇔ C) → (B ⇔ D) → ((OP A B) ⇔ (OP C D)))
                        → (∀ {ℓ ℓ' ℓ'' ℓ''' : Level}{A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}
                          → (A ⇔ C) → (B ⇔ D) → ((OP' A B) ⇔ (OP' C D)))
SUBST⇔-lemma OP OP' OP⟷OP' substOP {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD =
  A⟺B→A⇔B (SUBST⟺-lemma OP OP' (A⇔B→A⟺B  OP⟷OP')
  (λ u v → A⇔B→A⟺B (substOP (A⟺B→A⇔B u) (A⟺B→A⇔B v)))
  (A⇔B→A⟺B AC) (A⇔B→A⟺B BD))

-- As before we want to be able to inductively prove such substitutions for at least all
-- classical proper terms, or, this time (as opposed to SUBST⟷-lemma), all terms that
-- are ⟺-equivalent to a classical proper term. To do this we show the necessary property
-- of substitution for the same set of basic classical proper operators as before:

-- A⟺B⟷¬¬A⟷B 

-- A (NOT' A)  Substitution lemma
A⟺B→NOTA⟺NOTB : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⟺ B) → (NOT A) ⟺ (NOT B)
A⟺B→NOTA⟺NOTB {ℓ} {ℓ'} {A} {B} ab = BtoA A⟺B⟷¬¬A⟷B  (A→B→¬¬A→¬¬B A⟷B→NOTA⟷NOTB (AtoB A⟺B⟷¬¬A⟷B ab))

-- A (NOT' A)  Substitution lemma 
A⟺B→NOT'A⟺NOT'B : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → (A ⟺ B) → (NOT' A) ⟺ (NOT' B)
A⟺B→NOT'A⟺NOT'B {ℓ} {ℓ'} {A} {B} ab =  BtoA A⟺B⟷¬¬A⟷B  (A→B→¬¬A→¬¬B A⟷B→NOT'A⟷NOT'B (AtoB A⟺B⟷¬¬A⟷B ab))

-- An (OR A B) Substitution lemma
A⟺C→B⟺D→ORAB⟺ORCD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟺ C) → (B ⟺ D) → (OR A B) ⟺ (OR C D)
A⟺C→B⟺D→ORAB⟺ORCD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A} {B} {C}{D} AC BD  =
  BtoA  A⟺B⟷¬¬A⟷B (A→B→C→¬¬A→¬¬B→¬¬C A⟷C→B⟷D→ORAB⟷ORCD (AtoB A⟺B⟷¬¬A⟷B AC) (AtoB  A⟺B⟷¬¬A⟷B BD))

-- An (OR' A B) Substitution lemma
A⟺C→B⟺D→OR'AB⟺OR'CD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟺ C) → (B ⟺ D) → (OR' A B) ⟺ (OR' C D)
A⟺C→B⟺D→OR'AB⟺OR'CD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A} {B} {C}{D} AC BD  =
  BtoA  A⟺B⟷¬¬A⟷B (A→B→C→¬¬A→¬¬B→¬¬C A⟷C→B⟷D→OR'AB⟷OR'CB (AtoB A⟺B⟷¬¬A⟷B AC) (AtoB  A⟺B⟷¬¬A⟷B BD))

-- AND A B Substitution lemma
A⟺C→B⟺D→ANDAB⟺ANDCD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟺ C) → (B ⟺ D) → (AND A B) ⟺ (AND C D)
A⟺C→B⟺D→ANDAB⟺ANDCD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A}{B}{C}{D} AC BD  =
  BtoA  A⟺B⟷¬¬A⟷B (A→B→C→¬¬A→¬¬B→¬¬C A⟷C→B⟷D→ANDAB⟷ANDCD (AtoB A⟺B⟷¬¬A⟷B AC) (AtoB  A⟺B⟷¬¬A⟷B BD))

-- AND' A B  Substitution lemma
A⟺C→B⟺D→AND'AB⟺AND'CD : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟺ C) → (B ⟺ D) → (AND' A B) ⟺ (AND' C D)
A⟺C→B⟺D→AND'AB⟺AND'CD {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A}{B}{C}{D} AC BD  =
  BtoA  A⟺B⟷¬¬A⟷B (A→B→C→¬¬A→¬¬B→¬¬C A⟷C→B⟷D→AND'AB⟷AND'CD (AtoB A⟺B⟷¬¬A⟷B AC) (AtoB A⟺B⟷¬¬A⟷B BD))

-- A ⇒ B  Substitution lemma
A⟺C→B⟺D→A⇒B⟺C⇒D : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟺ C) → (B ⟺ D) → (A ⇒ B) ⟺ (C ⇒ D)
A⟺C→B⟺D→A⇒B⟺C⇒D {ℓ} {ℓ'} {ℓ''} {ℓ'''} {A}{B}{C}{D} AC BD =
  BtoA  A⟺B⟷¬¬A⟷B (A→B→C→¬¬A→¬¬B→¬¬C A⟷C→B⟷D→A⇒B⟷C⇒D
        (AtoB (¬¬A⟷C→¬A⟷C'⟷⊥ (AtoB A⟺B⟷¬¬A⟷B AC)))
        (AtoB (¬¬A⟷C→¬A⟷C'⟷⊥ (AtoB A⟺B⟷¬¬A⟷B BD))))

-- A ⇔ B Substitution lemma
A⟺C→B⟺D→A⇔B⟺C⇔D :  {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟺ C) → (B ⟺ D) → (A ⇔ B) ⟺ (C ⇔ D)
A⟺C→B⟺D→A⇔B⟺C⇔D {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD =
  BtoA  A⟺B⟷¬¬A⟷B (A→B→C→¬¬A→¬¬B→¬¬C A⟷C→B⟷D→A⇔B⟷C⇔D
        (AtoB (¬¬A⟷C→¬A⟷C'⟷⊥ (AtoB A⟺B⟷¬¬A⟷B AC)))
        (AtoB (¬¬A⟷C→¬A⟷C'⟷⊥ (AtoB A⟺B⟷¬¬A⟷B BD))))
                                                           
-- And of course we can add an A ⟺ B Substitution lemma (as per _⟷_) :
A⟺C→B⟺D→A⟺B⟺C⇔D : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''} →
  (A ⟺ C) → (B ⟺ D) → (A ⟺ B) ⟺ (C ⟺ D)
A⟺C→B⟺D→A⟺B⟺C⇔D {ℓ}{ℓ'}{ℓ''}{ℓ'''} {A}{B}{C}{D} AC BD =
  BtoA  A⟺B⟷¬¬A⟷B (A→B→C→¬¬A→¬¬B→¬¬C A⟷C→B⟷D→A⟺B⟷C⟺D
        (AtoB (¬¬A⟷C→¬A⟷C'⟷⊥ (AtoB A⟺B⟷¬¬A⟷B AC)))
        (AtoB (¬¬A⟷C→¬A⟷C'⟷⊥ (AtoB A⟺B⟷¬¬A⟷B BD))))

