\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Bilimits.plus
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import UF.Base

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Bilimits.Sequential pt fe 𝓤₁ 𝓤₁
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe

open import Naturals.Order hiding (subtraction')
open import Naturals.Addition renaming (_+_ to _+'_)
open import Notation.Order

module _  (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) where
  comp+' :  (X + Y -> X + Y -> 𝓤₁ ̇)
  comp+' = {!!}

comp+ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) -> (X -> X -> 𝓤₁ ̇) ->  (Y -> Y -> 𝓤₁ ̇) -> (X + Y -> X + Y -> 𝓤₁ ̇)
comp+ X Y f g (inl z) (inl w) = f z w
comp+ X Y f g (inl z) (inr w) = 𝟘 
comp+ X Y f g (inr z) (inl w) = 𝟘 
comp+ X Y f g (inr z) (inr w) = g z w

valued+ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) -> ((x y : X) → is-prop(f x y)) -> ((x y : Y) → is-prop(g x y)) -> ((x y : X + Y) → is-prop((comp+ X Y f g) x y))
valued+ X Y f g p1 p2 (inl z) (inl w) = p1 z w
valued+ X Y f g p1 p2 (inl z) (inr w) = 𝟘-is-prop
valued+ X Y f g p1 p2 (inr z) (inl w) = 𝟘-is-prop
valued+ X Y f g p1 p2 (inr z) (inr w) = p2 z w

reflex+ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) -> ((x : X) -> f x x) -> ((y : Y) -> g y y) -> (x : X + Y) → comp+ X Y f g x x
reflex+ X Y f g r1 r2 (inl x) = r1 x
reflex+ X Y f g r1 r2 (inr x) = r2 x

transative+ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) -> ((x y z : X) → (f x y) → (f y z) → (f x z)) -> ((x y z : Y) → (g x y) → (g y z) → (g x z)) -> (x y z : X + Y) → (comp+ X Y f g x y) -> (comp+ X Y f g y z) -> (comp+ X Y f g x z)
transative+ X Y f g t1 t2 (inl x) (inl y) (inl z) e1 e2 = t1 x y z e1 e2
transative+ X Y f g t1 t2 (inr x) (inr y) (inr z) e1 e2 = t2 x y z e1 e2

anti+ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) -> ((x y : X) → (f x y) → (f y x) → x ＝ y) -> ((x y : Y) → (g x y) → (g y x) → x ＝ y) -> (x y : X + Y) → (comp+ X Y f g x y) → (comp+ X Y f g y x) → x ＝ y
anti+ X Y f g a1 a2 (inl x) (inl y) e1 e2 = ap inl (a1 x y e1 e2)
anti+ X Y f g a1 a2 (inr x) (inr y) e1 e2 = ap inr (a2 x y e1 e2)

split : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇) (α : I → X + Y) (i : I) -> (Σ x ꞉ X , (α i) ＝ (inl x)) + (Σ y ꞉ Y , (α i) ＝ (inr y))
split X Y I α i = splits (α i)
  where
   splits : (z : X + Y) -> (Σ x ꞉ X , z ＝ (inl x)) + (Σ y ꞉ Y , z ＝ (inr y))
   splits (inl x) = inl (x , refl)
   splits (inr y) = inr (y , refl)

{-left-}

ext-left : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇ ) (α : I → X + Y) (i : I)
  -> ((y : Y) (i : I) -> ((α i) ＝ (inr y)) -> 𝟘)
  -> (x : X + Y) -> ((α i) ＝ x) -> X
ext-left X Y I α i bad (inl x) p = x
ext-left X Y I α i bad (inr y) p = 𝟘-elim (bad y i p)

left : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇ ) (α : I → X + Y) -> ((y : Y) (i : I) -> ((α i) ＝ (inr y)) -> 𝟘) -> I -> X
left X Y I α bad i = ext-left X Y I α i bad (α i) refl

left-eq : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇) (α : I → X + Y) (bad : (y : Y) (i : I) -> ((α i) ＝ (inr y)) -> 𝟘) (i : I) -> (inl (left X Y I α bad i) ＝ (α i))
left-eq X Y I α bad i = ext (α i) refl
  where
   ext-left-eq : (x y : X + Y) (p : x ＝ y) (q : ((α i) ＝ x))-> (ext-left X Y I α i bad x q) ＝ (ext-left X Y I α i bad y (q ∙ p))
   ext-left-eq x x refl q = refl
   
   ext : (x : X + Y) -> ((α i) ＝ x) -> ((inl (left X Y I α bad i)) ＝ x)
   ext (inl x) p = ap inl (ext-left-eq (α i) (inl x) p refl)
   ext (inr y) p = 𝟘-elim (bad y i p)

left-neq : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇)  (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) (α : I → X + Y) (i1 : I) -> (Σ x ꞉ X , (α i1) ＝ (inl x)) -> ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k))) -> (y : Y) (j1 : I) -> ((α j1) ＝ (inr y)) -> 𝟘
left-neq X Y I f g α i1 p dir y j1 q = ∥∥-rec 𝟘-is-prop (left-neq2 p q ) (dir i1 j1)
  where
   case1 : ((α j1) ＝ (inr y)) -> (k : I) -> (comp+ X Y f g (α j1) (α k)) -> (Σ x ꞉ X , (α k) ＝ (inl x)) -> 𝟘
   case1 p k comp1 (x , q) = transport (comp+ X Y f g (inr y)) q (transport (λ z → comp+ X Y f g z (α k)) p comp1)

   case2 : (Σ x ꞉ X , (α i1) ＝ (inl x)) -> (k : I) -> (comp+ X Y f g (α i1) (α k)) -> (Σ y ꞉ Y , (α k) ＝ (inr y)) -> 𝟘
   case2 (x , p) k comp1 (y , q) = transport (comp+ X Y f g (inl x)) q (transport (λ z → comp+ X Y f g z (α k)) p comp1)

   left-neq2 : (Σ x ꞉ X , (α i1) ＝ (inl x)) -> ((α j1) ＝ (inr y)) -> Σ k ꞉ I , (comp+ X Y f g (α i1) (α k)) × (comp+ X Y f g (α j1) (α k)) -> 𝟘
   left-neq2 p q (k , (comp1 , comp2)) = cases (case1 q k comp2) (case2 p k comp1) (split X Y I α k)

left-semi : (X : 𝓤 ̇) (Y : 𝓥 ̇ ) (I : 𝓦 ̇)  (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) (α : I → X + Y) (b : I -> X) -> ((i : I) -> (inl (b i) ＝ (α i))) -> ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k))) -> (i j : I) → ∃ k ꞉ I , (f (b i) (b k)) × (f (b j) (b k))
left-semi X Y I f g α b eq semi i j = (∥∥-functor (left-semi2 eq)) (semi i j)
  where
   left-semi2 : ((i : I) -> (inl (b i) ＝ (α i))) -> Σ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k)) -> Σ k ꞉ I , (f (b i) (b k)) × (f (b j) (b k))
   left-semi2 eq semi = ((pr₁ semi) , transport (λ z → (comp+ X Y f g z (inl (b (pr₁ semi)))) × (comp+ X Y f g (inl (b j)) (inl (b (pr₁ semi))))) ((eq i)⁻¹) (transport (λ z → (comp+ X Y f g (α i) (inl (b (pr₁ semi)))) × (comp+ X Y f g z (inl (b (pr₁ semi))))) ((eq j)⁻¹) (transport (λ z → (comp+ X Y f g (α i) z) × (comp+ X Y f g (α j) z)) ((eq (pr₁ semi))⁻¹) (pr₂ semi))))

left-sup :  (X : 𝓤 ̇) (Y : 𝓥 ̇ ) (I : 𝓦 ̇) (i1 : I) (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) (α : I → X + Y) (b : I -> X) -> ((i : I) -> (inl (b i) ＝ (α i))) -> (Σ s ꞉ X , (((i : I) → (f (b i) s)) × ((v : X) → ((i : I) → (f (b i) v)) → (f s v)))) -> (Σ s ꞉ X + Y , (((i : I) → (comp+ X Y f g (α i) s)) × ((v : X + Y) → ((i : I) → (comp+ X Y f g (α i) v)) → (comp+ X Y f g s v))))

left-sup X Y I i1 f g α b eq (s , (up , low)) = (inl s , ((λ i -> transport (λ z -> (comp+ X Y f g z (inl s))) (eq i) (up i)) , dep-cases (λ v func -> low v (λ i -> transport (λ z -> (comp+ X Y f g z (inl v))) ((eq i)⁻¹) (func i))) (λ v func -> 𝟘-elim (transport (λ z -> (comp+ X Y f g z (inr v))) ((eq i1)⁻¹) (func i1)) ) ))

{-right-}

ext-right : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇ ) (α : I → X + Y) (i : I) -> ((x : X) (i : I) -> ((α i) ＝ (inl x)) -> 𝟘) -> (y : X + Y) -> ((α i) ＝ y) -> Y
ext-right X Y I α i bad (inr y) p = y
ext-right X Y I α i bad (inl x) p = 𝟘-elim (bad x i p)

right : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇ ) (α : I → X + Y) -> ((x : X) (i : I) -> ((α i) ＝ (inl x)) -> 𝟘) -> I -> Y
right X Y I α bad i = ext-right X Y I α i bad (α i) refl

right-eq : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇) (α : I → X + Y) (bad : (x : X) (i : I) -> ((α i) ＝ (inl x)) -> 𝟘) (i : I) -> (inr (right X Y I α bad i) ＝ (α i))
right-eq X Y I α bad i = ext (α i) refl
  where
   ext-right-eq : (x y : X + Y) (p : x ＝ y) (q : ((α i) ＝ x))-> (ext-right X Y I α i bad x q) ＝ (ext-right X Y I α i bad y (q ∙ p))
   ext-right-eq x x refl q = refl
   
   ext : (x : X + Y) -> ((α i) ＝ x) -> ((inr (right X Y I α bad i)) ＝ x)
   ext (inr y) p = ap inr (ext-right-eq (α i) (inr y) p refl)
   ext (inl x) p = 𝟘-elim (bad x i p)


right-neq : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (I : 𝓦 ̇)  (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) (α : I → X + Y) (i1 : I) -> (Σ x ꞉ Y , (α i1) ＝ (inr x)) -> ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k))) -> (y : X) (j1 : I) -> ((α j1) ＝ (inl y)) -> 𝟘
right-neq X Y I f g α i1 p dir y j1 q = ∥∥-rec 𝟘-is-prop (right-neq2 p q ) (dir i1 j1)
  where
   case1 : ((α j1) ＝ (inl y)) -> (k : I) -> (comp+ X Y f g (α j1) (α k)) -> (Σ x ꞉ Y , (α k) ＝ (inr x)) -> 𝟘
   case1 p k comp1 (x , q) = transport (comp+ X Y f g (inl y)) q (transport (λ z → comp+ X Y f g z (α k)) p comp1)

   case2 : (Σ x ꞉ Y , (α i1) ＝ (inr x)) -> (k : I) -> (comp+ X Y f g (α i1) (α k)) -> (Σ y ꞉ X , (α k) ＝ (inl y)) -> 𝟘
   case2 (x , p) k comp1 (y , q) = transport (comp+ X Y f g (inr x)) q (transport (λ z → comp+ X Y f g z (α k)) p comp1)

   right-neq2 : (Σ x ꞉ Y , (α i1) ＝ (inr x)) -> ((α j1) ＝ (inl y)) -> Σ k ꞉ I , (comp+ X Y f g (α i1) (α k)) × (comp+ X Y f g (α j1) (α k)) -> 𝟘
   right-neq2 p q (k , (comp1 , comp2)) = cases (case2 p k comp1) (case1 q k comp2) (split X Y I α k)


right-semi : (X : 𝓤 ̇) (Y : 𝓥 ̇ ) (I : 𝓦 ̇)  (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) (α : I → X + Y) (b : I -> Y) -> ((i : I) -> (inr (b i) ＝ (α i))) -> ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k))) -> (i j : I) → ∃ k ꞉ I , (g (b i) (b k)) × (g (b j) (b k))
right-semi X Y I f g α b eq semi i j = (∥∥-functor (right-semi2 eq)) (semi i j)
  where
   right-semi2 : ((i : I) -> (inr (b i) ＝ (α i))) -> Σ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k)) -> Σ k ꞉ I , (g (b i) (b k)) × (g (b j) (b k))
   right-semi2 eq semi = ((pr₁ semi) , transport (λ z → (comp+ X Y f g z (inr (b (pr₁ semi)))) × (comp+ X Y f g (inr (b j)) (inr (b (pr₁ semi))))) ((eq i)⁻¹) (transport (λ z → (comp+ X Y f g (α i) (inr (b (pr₁ semi)))) × (comp+ X Y f g z (inr (b (pr₁ semi))))) ((eq j)⁻¹) (transport (λ z → (comp+ X Y f g (α i) z) × (comp+ X Y f g (α j) z)) ((eq (pr₁ semi))⁻¹) (pr₂ semi))))

right-sup :  (X : 𝓤 ̇) (Y : 𝓥 ̇ ) (I : 𝓦 ̇) (i1 : I) (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇) (α : I → X + Y) (b : I -> Y) -> ((i : I) -> (inr (b i) ＝ (α i))) -> (Σ s ꞉ Y , (((i : I) → (g (b i) s)) × ((v : Y) → ((i : I) → (g (b i) v)) → (g s v)))) -> (Σ s ꞉ X + Y , (((i : I) → (comp+ X Y f g (α i) s)) × ((v : X + Y) → ((i : I) → (comp+ X Y f g (α i) v)) → (comp+ X Y f g s v))))

right-sup X Y I i1 f g α b eq (s , (up , low)) = (inr s , ((λ i -> transport (λ z -> (comp+ X Y f g z (inr s))) (eq i) (up i)) , dep-cases (λ v func -> 𝟘-elim (transport (λ z -> (comp+ X Y f g z (inl v))) ((eq i1)⁻¹) (func i1)) ) (λ v func -> low v (λ i -> transport (λ z -> (comp+ X Y f g z (inr v))) ((eq i)⁻¹) (func i))) ))

directed+ : ( 𝓦 : Universe ) (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
          (f : X -> X -> 𝓤₁ ̇) (g : Y -> Y -> 𝓤₁ ̇)
          -> ((I : 𝓦 ̇ ) (α : I → X) → ((∥_∥ I) × ((i j : I) → ∃ k ꞉ I , (f (α i) (α k)) × (f (α j) (α k)))) → (Σ s ꞉ X , (((i : domain α) → (f (α i) s)) × ((v : X) → ((i : domain α) → (f (α i) v)) → (f s v)))))
          -> ((I : 𝓦 ̇ ) (α : I → Y) → ((∥_∥ I) × ((i j : I) → ∃ k ꞉ I , (g (α i) (α k)) × (g (α j) (α k)))) → (Σ s ꞉ Y , (((i : domain α) → (g (α i) s)) × ((v : Y) → ((i : domain α) → (g (α i) v)) → (g s v)))))
          -> (I : 𝓦 ̇ ) (α : I → X + Y)
          → is-prop (((∥_∥ I) × ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k)))) -> (Σ s ꞉ X + Y , (((i : domain α) → (comp+ X Y f g (α i) s)) × ((v : X + Y) → ((i : domain α) → (comp+ X Y f g (α i) v)) → (comp+ X Y f g s v))))) -> ((∥_∥ I) × ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k)))) -> (Σ s ꞉ X + Y , (((i : domain α) → (comp+ X Y f g (α i) s)) × ((v : X + Y) → ((i : domain α) → (comp+ X Y f g (α i) v)) → (comp+ X Y f g s v))))

directed+ 𝓦 X Y f g c1 c2 I α prp (dir0 , dir1) = ((∥∥-rec prp (λ i1 -> cases (left-dir i1 c1) (right-dir i1 c2) (split X Y I α i1))) dir0) (dir0 , dir1)
  where
   left-dir : (i1 : I) -> ((J : 𝓦 ̇ ) (α1 : J → X) → ((∥_∥ J) × ((i j : J) → ∃ k ꞉ J , (f (α1 i) (α1 k)) × (f (α1 j) (α1 k)))) → (Σ s ꞉ X , (((i : domain α1) → (f (α1 i) s)) × ((v : X) → ((i : domain α1) → (f (α1 i) v)) → (f s v))))) → (Σ x ꞉ X , (α i1) ＝ (inl x)) -> (∥_∥ I) × ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k))) → (Σ s ꞉ X + Y , (((i : domain α) → (comp+ X Y f g (α i) s)) × ((v : X + Y) → ((i : domain α) → (comp+ X Y f g (α i) v)) → (comp+ X Y f g s v))))

   left-dir i1 c1 p (dir0 , dir) =
     let  b : I -> X
          b = left X Y I α (left-neq X Y I f g α i1 p dir)
          eq : (i : I) -> (inl (b i) ＝ (α i))
          eq = left-eq X Y I α (left-neq X Y I f g α i1 p dir)
          
     in left-sup X Y I i1 f g α b eq (c1 I b (∣_∣ i1 , left-semi X Y I f g α b eq dir))

   right-dir : (i1 : I) -> ((J : 𝓦 ̇ ) (α1 : J → Y) → ((∥_∥ J) × ((i j : J) → ∃ k ꞉ J , (g (α1 i) (α1 k)) × (g (α1 j) (α1 k)))) → (Σ s ꞉ Y , (((i : domain α1) → (g (α1 i) s)) × ((v : Y) → ((i : domain α1) → (g (α1 i) v)) → (g s v))))) → (Σ y ꞉ Y , (α i1) ＝ (inr y)) -> (∥_∥ I) × ((i j : I) → ∃ k ꞉ I , (comp+ X Y f g (α i) (α k)) × (comp+ X Y f g (α j) (α k))) → (Σ s ꞉ X + Y , (((i : domain α) → (comp+ X Y f g (α i) s)) × ((v : X + Y) → ((i : domain α) → (comp+ X Y f g (α i) v)) → (comp+ X Y f g s v))))

   right-dir i1 c1 p (dir0 , dir) =
     let  b : I -> Y
          b = right X Y I α (right-neq X Y I f g α i1 p dir)
          eq : (i : I) -> (inr (b i) ＝ (α i))
          eq = right-eq X Y I α (right-neq X Y I f g α i1 p dir)
          
     in right-sup X Y I i1 f g α b eq (c1 I b (∣_∣ i1 , right-semi X Y I f g α b eq dir))


plus : DCPO {𝓤₁} {𝓤₁} -> DCPO {𝓤₁} {𝓤₁} -> DCPO {𝓤₁} {𝓤₁}
plus  (D1 , _⊑1_ , (s1 , p1 , r1 , t1 , a1) , c1)  (D2 , _⊑2_ , (s2 , p2 , r2 , t2 , a2) , c2) = ( (D1 + D2) , comp+ D1 D2 _⊑1_ _⊑2_ , (+-is-set D1 D2 s1 s2 , valued+ D1 D2 _⊑1_ _⊑2_ p1 p2 , reflex+ D1 D2 _⊑1_ _⊑2_ r1 r2 , transative+ D1 D2 _⊑1_ _⊑2_ t1 t2 , anti+  D1 D2 _⊑1_ _⊑2_ a1 a2) , {!!})
  -- where
  --  directed+ 

\end{code}

{-
_plus_ : DCPO⊥ {𝓤₁} {𝓤₁} -> DCPO⊥ {𝓤₁} {𝓤₁} -> DCPO⊥ {𝓤₁} {𝓤₁}

 = (D1 + D2 , _⊑2_ , (s2 , p2 , r2 , t2 , a2) , c2)

( +-is-set s1 s2)
-}
