
{-# OPTIONS --safe #-}
{-# OPTIONS --cubical  #-}
{-# OPTIONS --guardedness #-}

module Logic.Conversions where

open import Cubical.Foundations.Prelude as C
open import Cubical.Foundations.Isomorphism
open import Data.Empty
open import Data.Nat.Base as ℕ using (ℕ ; suc; zero; _^_; pred ) renaming (_⊔_ to max)
open import Relation.Nullary.Negation.Core
open import Relation.Binary.PropositionalEquality.Core renaming (_≡_ to _≣_ ; refl to Refl ; cong to cong' ; sym to sym')
open import Cubical.Data.Nat using (isZero)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Logic.Classical.Base using (ISTRUE ; converse ; _⟷_ ) renaming (isProp to isProp' ; isProp¬ to isProp¬')

private 
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
private
  variable
    n : ℕ
    A : Set ℓ
    B : Set ℓ'
    C : Set ℓ''

-----------------------------------------------------

contra : true ≡ false → ⊥
contra contra = C.subst typelemma contra true
  where
    typelemma : Bool → Type
    typelemma false = ⊥
    typelemma true = Bool

compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ{ j (i = i0) → x
                                 ; j (i = i1) → q j })
                               (p i)

isProp¬ : {A : Type ℓ} → isProp (¬ A)
isProp¬ x y i = x

isProp∀¬¬ : {A : Type ℓ} → {B : A → Type ℓ'} → isProp (∀ (a : A) → ISTRUE (B a))
isProp∀¬¬ {ℓ}{ℓ'}{A}{B} x y i a z = cong (\za → za z) xa≡ya i
                           where
                             xa≡ya : (x a) ≡ (y a)
                             xa≡ya = isProp¬ (x a) (y a)

--------------------

a≣b→b≡c→a≡c : {A : Type ℓ} {a b c : A} ->  a ≣ b → b ≡ c → a ≡ c
a≣b→b≡c→a≡c {ℓ} {A} {a} {b} {c} Refl bc = bc

a≣b→a≡b : {A : Type ℓ} {a b : A} ->  a ≣ b → a ≡ b 
a≣b→a≡b {ℓ}{A} {a} {b} Refl = refl

a≡b→a≣b-ℕ : {a b : ℕ} -> a ≡ b → a ≣ b
a≡b→a≣b-ℕ {zero} {zero} ab = Refl
a≡b→a≣b-ℕ {zero} {suc b} ab = ⊥-elim (contra tf)
              where
                tf : true ≡ false
                tf = cong isZero ab
a≡b→a≣b-ℕ {suc a} {zero} ab = ⊥-elim (contra tf)
              where
                tf : true ≡ false
                tf = C.sym (cong isZero ab)
a≡b→a≣b-ℕ {suc a} {suc b} ab = cong' suc (a≡b→a≣b-ℕ ab') 
              where
                ab' : a ≡ b
                ab' = cong pred ab

¬a≡b→¬a≣b : {A : Type ℓ} {a b : A} → ¬ (a ≡ b) → ¬ (a ≣ b)
¬a≡b→¬a≣b {ℓ}{A}{a}{b} nab = converse a≣b→a≡b nab

¬a≣b→¬a≡b-ℕ : {a b : ℕ} → ¬ (a ≣ b) → ¬ (a ≡ b)
¬a≣b→¬a≡b-ℕ {a}{b} nab = converse a≡b→a≣b-ℕ nab

-------------------------------------

isProp'→isProp : {A : Type ℓ} → isProp' A → isProp A
isProp'→isProp {ℓ} {A} ispA = λ x y → let x≣y = ispA x y in a≣b→a≡b x≣y

A⟷BisProps : {ℓ : Level} {A B : Set ℓ} → (A ⟷ B) → isProp A → isProp B → A ≡ B
A⟷BisProps {ℓ} {A} {B} record { AtoB = AtoB ; BtoA = BtoA } ispA ispB =
  isoToPath (iso AtoB BtoA (λ b → ispB (AtoB (BtoA b)) b) λ a → ispA (BtoA (AtoB a)) a)

-------------------------------------

cubical≡-∀lemma : {ℓ ℓ' : Level} {A : Set ℓ} →
  (f g :  A → Set ℓ') → (∀ (a : A) → (f a) ≡ (g a)) → (∀ (a : A) → f a) ≡ (∀ (a : A) → g a)
cubical≡-∀lemma {ℓ}{ℓ'}{A} f g fg = cong (λ f' → (∀ (a : A) → f' a)) f≡g 
  where
    f≡g : f ≡ g
    f≡g = funExt fg

------------------------------------
