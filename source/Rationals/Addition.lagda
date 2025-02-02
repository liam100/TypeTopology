Andrew Sneap, Jan-July 2021

In this file I define addition of rational numbers, and prove
properties of addition.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe  --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import UF.Base hiding (_≈_)
open import UF.FunExt

open import Integers.Type
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (_+_ to _ℚₙ+_)
open import Rationals.Type

module Rationals.Addition where

_+_ : ℚ → ℚ → ℚ
(p , _) + (q , _) = toℚ (p ℚₙ+ q)

infixl 32 _+_

ℚ+-comm : (p q : ℚ) → p + q ＝ q + p
ℚ+-comm (p , _) (q , _) = ap toℚ I
 where
  I : p ℚₙ+ q ＝ q ℚₙ+ p
  I = ℚₙ+-comm p q

toℚ-+ : Fun-Ext → (p q : ℚₙ) → toℚ (p ℚₙ+ q) ＝ toℚ p + toℚ q
toℚ-+ fe p q = equiv→equality fe (p ℚₙ+ q) (p' ℚₙ+ q') conclusion
 where
  p-ℚ = toℚ p
  q-ℚ = toℚ q
  p' = toℚₙ p-ℚ
  q' = toℚₙ q-ℚ

  I : p ≈ p'
  I = ≈-toℚ p

  II : q ≈ q'
  II = ≈-toℚ q

  III : p ℚₙ+ q ≈ p' ℚₙ+ q
  III = ≈-addition p p' q I

  IV : q ℚₙ+ p' ≈ q' ℚₙ+ p'
  IV = ≈-addition  q q' p' II

  V : p' ℚₙ+ q ≈ p' ℚₙ+ q'
  V = transport₂ _≈_ (ℚₙ+-comm q p') (ℚₙ+-comm q' p') IV

  conclusion : p ℚₙ+ q ≈ p' ℚₙ+ q'
  conclusion = ≈-trans (p ℚₙ+ q) (p' ℚₙ+ q) (p' ℚₙ+ q') III V

ℚ+-assoc : Fun-Ext → (p q r : ℚ) → p + q + r ＝ p + (q + r)
ℚ+-assoc fe (x , p) (y , q) (z , r) = V
 where
  α β : ℚ
  α = toℚ (x ℚₙ+ y)
  β = toℚ (y ℚₙ+ z)

  III : Σ r' ꞉ ℚₙ , (z , r ＝ toℚ r')
  III = q-has-qn fe (z , r)
  r' = pr₁ III
  rp = pr₂ III

  IV : Σ p' ꞉ ℚₙ , (x , p ＝ toℚ p')
  IV = q-has-qn fe (x , p)
  p' = pr₁ IV
  pp = pr₂ IV

  V : toℚ (x ℚₙ+ y) + (z , r) ＝ (x , p) + ((y , q) + (z , r))
  V =  α + (z , r)          ＝⟨ ap (α +_) rp             ⟩
       α + toℚ r'           ＝⟨ toℚ-+ fe (x ℚₙ+ y) r' ⁻¹  ⟩
       toℚ (x ℚₙ+ y ℚₙ+ z)   ＝⟨ ap toℚ (ℚₙ+-assoc x y z) ⟩
       toℚ (x ℚₙ+ (y ℚₙ+ z)) ＝⟨ toℚ-+ fe p' (y ℚₙ+ z)    ⟩
       toℚ p' + β           ＝⟨ ap (_+ β) (pp ⁻¹)        ⟩
       (x , p) + β ∎

ℚ+-rearrange : Fun-Ext → (x y z : ℚ) → x + y + z ＝ x + z + y
ℚ+-rearrange fe x y z = x + y + z     ＝⟨ ℚ+-assoc fe x y z       ⟩
                        x + (y + z)   ＝⟨ ap (x +_) (ℚ+-comm y z) ⟩
                        x + (z + y)   ＝⟨ ℚ+-assoc fe x z y ⁻¹    ⟩
                        x + z + y     ∎

ℚ+-rearrange' : Fun-Ext → (x y z : ℚ) → x + y + z ＝ z + x + y
ℚ+-rearrange' fe x y z = x + y + z   ＝⟨ ℚ+-comm (x + y) z    ⟩
                         z + (x + y) ＝⟨ ℚ+-assoc fe z x y ⁻¹ ⟩
                         z + x + y   ∎

ℚ-zero-left-neutral : Fun-Ext → (q : ℚ) → 0ℚ + q ＝ q
ℚ-zero-left-neutral fe q = II
 where
  I : Σ q' ꞉ ℚₙ , q ＝ toℚ q'
  I = q-has-qn fe q

  q' : ℚₙ
  q' = pr₁ I

  II : 0ℚ + q ＝ q
  II = 0ℚ + q                   ＝⟨ refl                              ⟩
       toℚ ((pos 0 , 0) ℚₙ+ q') ＝⟨ ap toℚ (ℚₙ+-comm (pos 0 , 0) q')  ⟩
       toℚ (q' ℚₙ+ (pos 0 , 0)) ＝⟨ ap toℚ (ℚₙ-zero-right-neutral q') ⟩
       toℚ q'                   ＝⟨ pr₂ I ⁻¹ ⟩
       q                        ∎

ℚ-zero-right-neutral : Fun-Ext → (q : ℚ) → q + 0ℚ ＝ q
ℚ-zero-right-neutral fe q = ℚ+-comm q 0ℚ ∙ (ℚ-zero-left-neutral fe q)

open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Multiplication

add-same-denom : Fun-Ext → ((x , a) (y , a) : ℚₙ) → toℚ (x , a) + toℚ (y , a) ＝ toℚ (x ℤ+ y , a)
add-same-denom fe (x , a) (y , b) = I ⁻¹ ∙ equiv→equality fe ((x , b) ℚₙ+ (y , b)) (x ℤ+ y , b) II
 where
  I : toℚ ((x , b) ℚₙ+ (y , b)) ＝ toℚ (x , b) + toℚ (y , b)
  I = toℚ-+ fe (x , b) (y , b)
  II : (x , b) ℚₙ+ (y , b) ≈ (x ℤ+ y , b)
  II = ℚₙ-add-same-denom (x , b) (y , b)

1/3+1/3 : Fun-Ext → 1/3 + 1/3 ＝ 2/3
1/3+1/3 fe = add-same-denom fe (pos 1 , 2) (pos 1 , 2)

1/4+1/4 : Fun-Ext → 1/4 + 1/4 ＝ 1/2
1/4+1/4 fe = add-same-denom fe (pos 1 , 3) (pos 1 , 3) ∙ equiv→equality fe (pos 2 , 3) (pos 1 , 1) refl

1/2+1/4 : Fun-Ext → 1/2 + 1/4 ＝ 3/4
1/2+1/4 fe = equiv→equality fe ((pos 1 , 1) ℚₙ+ (pos 1 , 3)) (pos 3 , 3) refl

\end{code}

For the following code, the flag --experimentay-lossy-unification must
be added, otherwise the file compiles infinitely.

\begin{code}

1/4+3/4 : Fun-Ext → 1/4 + 3/4 ＝ 1ℚ
1/4+3/4 fe = I ⁻¹ ∙ equiv→equality fe ((pos 1 , 3) ℚₙ+ (pos 3 , 3)) (pos 1 , 0) refl
 where
  abstract
   I : toℚ ((pos 1 , 3) ℚₙ+ (pos 3 , 3)) ＝  toℚ (pos 1 , 3) + toℚ (pos 3 , 3)
   I = toℚ-+ fe (pos 1 , 3) (pos 3 , 3)

1/3+2/3 : Fun-Ext → 1/3 + 2/3 ＝ 1ℚ
1/3+2/3 fe = I ∙ equiv→equality fe (pos 3 , 2) (pos 1 , 0) refl
 where
  abstract
   I : toℚ (pos 1 , 2) + toℚ (pos 2 , 2) ＝ toℚ (pos 1 ℤ+ pos 2 , 2)
   I = add-same-denom fe (pos 1 , 2) (pos 2 , 2)


1/2+1/2 : Fun-Ext → 1/2 + 1/2 ＝ 1ℚ
1/2+1/2 fe = 1/2 + 1/2                         ＝⟨ refl ⟩
             toℚ ((pos 1 , 1) ℚₙ+ (pos 1 , 1)) ＝⟨ equiv→equality fe ((pos 1 , 1) ℚₙ+ (pos 1 , 1)) (pos 1 , 0) by-definition ⟩
             toℚ (pos 1 , 0)                   ＝⟨ refl ⟩
             1ℚ ∎

1/5+1/5 : Fun-Ext → 1/5 + 1/5 ＝ 2/5
1/5+1/5 fe = I
 where
  abstract
   I : 1/5 + 1/5 ＝ 2/5
   I = add-same-denom fe (pos 1 , 4) (pos 1 , 4)

1/5+2/5 : Fun-Ext → 1/5 + 2/5 ＝ 3/5
1/5+2/5 fe = I
 where
  abstract
   I : 1/5 + 2/5 ＝ 3/5
   I = add-same-denom fe (pos 1 , 4) (pos 2 , 4)

2/5+1/5 : Fun-Ext → 2/5 + 1/5 ＝ 3/5
2/5+1/5 fe = (ℚ+-comm 2/5 1/5) ∙ (1/5+2/5 fe)

2/5+3/5-lemma : Fun-Ext → toℚ (pos 2 , 4) + toℚ (pos 3 , 4) ＝ toℚ (pos 2 ℤ+ pos 3 , 4)
2/5+3/5-lemma fe = I
 where
  abstract
   I : toℚ (pos 2 , 4) + toℚ (pos 3 , 4) ＝ toℚ (pos 2 ℤ+ pos 3 , 4)
   I = add-same-denom fe (pos 2 , 4) (pos 3 , 4)

2/5+3/5 : Fun-Ext → 2/5 + 3/5 ＝ 1ℚ
2/5+3/5 fe = I
 where
  abstract
   I : 2/5 + 3/5 ＝ 1ℚ
   I = 2/5+3/5-lemma fe ∙ equiv→equality fe (pos 5 , 4) (pos 1 , 0) refl

\end{code}
