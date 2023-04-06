\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Bilimits.plus2
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe
open import DomainTheory.Lifting.LiftingDcpo pt fe 𝓤₀ pe
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
open import Lifting.Lifting 𝓤₀ hiding (⊥)

open import Naturals.Order

{- open import Naturals.Order hiding (subtraction')
open import Naturals.Addition renaming (_+_ to _+'_)
open import Notation.Order -}

open import UF.Base
open import UF.UniverseEmbedding

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀

module _ (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) where
  D+E = ⟨ 𝓓 ⟩ + ⟨ 𝓔 ⟩

  _⊑_ : D+E → D+E → 𝓣 ⊔ 𝓣' ̇ 
  inl d ⊑ inl d' = Lift 𝓣' (d ⊑⟨ 𝓓 ⟩ d') -- d ⊑⟨ 𝓓 ⟩ d'
  inl d ⊑ inr e' = 𝟘
  inr e ⊑ inl d' = 𝟘
  inr e ⊑ inr e' = Lift 𝓣 (e ⊑⟨ 𝓔 ⟩ e')

  ⊑-is-prop-valued : (s t : D+E) → is-prop (s ⊑ t)
  ⊑-is-prop-valued (inl d) (inl d') = Σ-is-prop (prop-valuedness 𝓓 d d') (λ _ → 𝟙-is-prop)
  ⊑-is-prop-valued (inl d) (inr e') = 𝟘-is-prop
  ⊑-is-prop-valued (inr e) (inl d') = 𝟘-is-prop
  ⊑-is-prop-valued (inr e) (inr e') = Σ-is-prop (prop-valuedness 𝓔 e e') (λ _ → 𝟙-is-prop)

  ⊑-is-reflexive : (s : D+E) → s ⊑ s
  ⊑-is-reflexive = dep-cases (λ s → lift 𝓣' (reflexivity 𝓓 s)) (λ s → lift 𝓣 (reflexivity 𝓔 s))

  ⊑-is-transitive : (s t r : D+E) → s ⊑ t → t ⊑ r → s ⊑ r
  ⊑-is-transitive (inl s) (inl t) (inl r) p q = lift 𝓣' (transitivity 𝓓 s t r (lower p) (lower q))
  ⊑-is-transitive (inr s) (inr t) (inr r) p q = lift 𝓣 (transitivity 𝓔 s t r (lower p) (lower q))

  ⊑-is-antisymmetric : (s t : D+E) → s ⊑ t → t ⊑ s → s ＝ t
  ⊑-is-antisymmetric (inl s) (inl t) p q = ap inl (antisymmetry 𝓓 s t (lower p) (lower q))
  ⊑-is-antisymmetric (inr s) (inr t) p q = ap inr (antisymmetry 𝓔 s t (lower p) (lower q))




  -- Can't use is-continuous in the type annotation because we haven't
  -- constructed +-DCPO yet, but this type is definitionally equal to
  -- is-continuous 𝓓 +-DCPO inl
  inl-is-continuous : (I : 𝓤₀ ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                         → is-sup _⊑_ (inl (∐ 𝓓 δ)) (inl ∘ α)
  inl-is-continuous I α δ = (λ i → lift 𝓣' (∐-is-upperbound 𝓓 δ i)) , dep-cases (λ v x → lift 𝓣' (∐-is-lowerbound-of-upperbounds 𝓓 δ v (λ i → lower (x i)))) (λ v x -> ∥∥-rec 𝟘-is-prop x (pr₁ δ))


  inr-is-continuous : (I : 𝓤₀ ̇ ) (α : I → ⟨ 𝓔 ⟩) (δ : is-Directed 𝓔 α)
                         → is-sup _⊑_ (inr (∐ 𝓔 δ)) (inr ∘ α)
  inr-is-continuous I α δ = (λ i → lift 𝓣 (∐-is-upperbound 𝓔 δ i)) , dep-cases (λ v x -> ∥∥-rec 𝟘-is-prop x (pr₁ δ)) (λ v x → lift 𝓣 (∐-is-lowerbound-of-upperbounds 𝓔 δ v (λ i → lower (x i))))



  +-DCPO : DCPO {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
  +-DCPO = (D+E , _⊑_ , (+-is-set ⟨ 𝓓 ⟩ ⟨ 𝓔 ⟩ (sethood 𝓓) (sethood 𝓔)
                      , ⊑-is-prop-valued
                      , ⊑-is-reflexive
                      , ⊑-is-transitive
                      , ⊑-is-antisymmetric)
                , γ)
    where
      
      γ : is-directed-complete _⊑_ 
      γ I α (inh , semi) = ∥∥-rec (having-sup-is-prop _⊑_ (
        (+-is-set ⟨ 𝓓 ⟩ ⟨ 𝓔 ⟩ (sethood 𝓓) (sethood 𝓔)) ,
        ⊑-is-prop-valued ,
        ⊑-is-reflexive ,
        ⊑-is-transitive ,
        ⊑-is-antisymmetric) α)
        (λ i -> (dep-cases (leftcase i) (rightcase i) (split i))) inh
        where

          split : (i : I) -> (Σ x ꞉ ⟨ 𝓓 ⟩ , (α i) ＝ (inl x)) + (Σ y ꞉ ⟨ 𝓔 ⟩ , (α i) ＝ (inr y))
          split i = splits (α i)
            where
              splits : (z : D+E) -> (Σ x ꞉ ⟨ 𝓓 ⟩ , z ＝ (inl x)) + (Σ y ꞉ ⟨ 𝓔 ⟩ , z ＝ (inr y))
              splits (inl x) = inl (x , refl)
              splits (inr y) = inr (y , refl)

          {-left-}
          ext-left : (i : I) -> ((y : ⟨ 𝓔 ⟩) (i : I) -> ((α i) ＝ (inr y)) -> 𝟘) -> (x : D+E) -> ((α i) ＝ x) -> ⟨ 𝓓 ⟩
          ext-left i bad (inl x) p = x
          ext-left i bad (inr y) p = 𝟘-elim (bad y i p)

          left : ((y : ⟨ 𝓔 ⟩) (i : I) -> ((α i) ＝ (inr y)) -> 𝟘) -> I -> ⟨ 𝓓 ⟩
          left bad i = ext-left i bad (α i) refl

          left-eq : (bad : (y : ⟨ 𝓔 ⟩) (i : I) -> ((α i) ＝ (inr y)) -> 𝟘) (i : I) -> (inl (left bad i) ＝ (α i))
          left-eq bad i = ext (α i) refl
            where
              ext-left-eq : (x y : D+E) (p : x ＝ y) (q : ((α i) ＝ x)) -> (ext-left i bad x q) ＝ (ext-left i bad y (q ∙ p))
              ext-left-eq x x refl q = refl
   
              ext : (x : D+E) -> ((α i) ＝ x) -> ((inl (left bad i)) ＝ x)
              ext (inl x) p = ap inl (ext-left-eq (α i) (inl x) p refl)
              ext (inr y) p = 𝟘-elim (bad y i p)

          left-neq : (i1 : I) -> (Σ x ꞉ ⟨ 𝓓 ⟩ , (α i1) ＝ (inl x)) -> (y : ⟨ 𝓔 ⟩) (j1 : I) -> ((α j1) ＝ (inr y)) -> 𝟘
          left-neq i1 p y j1 q = ∥∥-rec 𝟘-is-prop (left-neq2 p q) (semi i1 j1)
            where
              case1 : ((α j1) ＝ (inr y)) -> (k : I) -> (α j1 ⊑ α k) -> (Σ x ꞉ ⟨ 𝓓 ⟩ , (α k) ＝ (inl x)) -> 𝟘
              case1 p k comp1 (x , q) = transport (_⊑_ (inr y)) q (transport (λ z → z ⊑ (α k)) p comp1)

              case2 : (Σ x ꞉ ⟨ 𝓓 ⟩ , (α i1) ＝ (inl x)) -> (k : I) -> (α i1 ⊑ α k) -> (Σ y ꞉ ⟨ 𝓔 ⟩ , (α k) ＝ (inr y)) -> 𝟘
              case2 (x , p) k comp1 (y , q) = transport (_⊑_ (inl x)) q (transport (λ z → z ⊑ (α k)) p comp1)

              left-neq2 : (Σ x ꞉ ⟨ 𝓓 ⟩ , (α i1) ＝ (inl x)) -> ((α j1) ＝ (inr y)) -> Σ k ꞉ I , (α i1 ⊑ α k) × (α j1 ⊑ α k) -> 𝟘
              left-neq2 p q (k , (comp1 , comp2)) = cases (case1 q k comp2) (case2 p k comp1) (split k)

          leftcase : (i1 : I) -> (Σ x ꞉ ⟨ 𝓓 ⟩ , (α i1) ＝ (inl x)) -> (has-sup _⊑_ α)
          leftcase i1 p = (inl (∐ 𝓓 d) , transport (λ z → is-sup _⊑_ (inl (∐ 𝓓 d)) z) eq (inl-is-continuous I b d))
            where
              b : I -> ⟨ 𝓓 ⟩
              b = left (left-neq i1 p)

              eq2 : (inl ∘ b) ∼ α
              eq2 = (left-eq (left-neq i1 p))
              
              eq : (inl ∘ b) ＝ α
              eq = (dfunext fe) eq2
              
              d : is-Directed 𝓓 b
              d = (∣_∣ i1 , λ i j → ∥∥-functor (λ (k , (p1 , p2)) → k , (lower (transport (λ z → inl (b i) ⊑ z) ((eq2 k)⁻¹) (transport (λ z → z ⊑ (α k)) ((eq2 i)⁻¹) p1)) , lower (transport (λ z → inl (b j) ⊑ z) ((eq2 k)⁻¹) (transport (λ z → z ⊑ (α k)) ((eq2 j)⁻¹) p2)))) (semi i j))


          {-right-}
          ext-right : (i : I) -> ((x : ⟨ 𝓓 ⟩) (i : I) -> ((α i) ＝ (inl x)) -> 𝟘) -> (y : D+E) -> ((α i) ＝ y) -> ⟨ 𝓔 ⟩
          ext-right i bad (inr y) p = y
          ext-right i bad (inl x) p = 𝟘-elim (bad x i p)

          right : ((x : ⟨ 𝓓 ⟩) (i : I) -> ((α i) ＝ (inl x)) -> 𝟘) -> I -> ⟨ 𝓔 ⟩
          right bad i = ext-right i bad (α i) refl

          right-eq : (bad : (x : ⟨ 𝓓 ⟩) (i : I) -> ((α i) ＝ (inl x)) -> 𝟘) (i : I) -> (inr (right bad i) ＝ (α i))
          right-eq bad i = ext (α i) refl
            where
              ext-right-eq : (x y : D+E) (p : x ＝ y) (q : ((α i) ＝ x))-> (ext-right i bad x q) ＝ (ext-right i bad y (q ∙ p))
              ext-right-eq x x refl q = refl
   
              ext : (x : D+E) -> ((α i) ＝ x) -> ((inr (right bad i)) ＝ x)
              ext (inr y) p = ap inr (ext-right-eq (α i) (inr y) p refl)
              ext (inl x) p = 𝟘-elim (bad x i p)


          right-neq : (i1 : I) -> (Σ x ꞉ ⟨ 𝓔 ⟩ , (α i1) ＝ (inr x)) -> (y : ⟨ 𝓓 ⟩) (j1 : I) -> ((α j1) ＝ (inl y)) -> 𝟘
          right-neq i1 p y j1 q = ∥∥-rec 𝟘-is-prop (right-neq2 p q ) (semi i1 j1)
            where
              case1 : ((α j1) ＝ (inl y)) -> (k : I) -> (α j1 ⊑ α k) -> (Σ x ꞉ ⟨ 𝓔 ⟩ , (α k) ＝ (inr x)) -> 𝟘
              case1 p k comp1 (x , q) = transport (_⊑_ (inl y)) q (transport (λ z →  z ⊑ (α k)) p comp1)

              case2 : (Σ x ꞉ ⟨ 𝓔 ⟩ , (α i1) ＝ (inr x)) -> (k : I) -> (α i1 ⊑ α k) -> (Σ y ꞉ ⟨ 𝓓 ⟩ , (α k) ＝ (inl y)) -> 𝟘
              case2 (x , p) k comp1 (y , q) = transport (_⊑_ (inr x)) q (transport (λ z → (z ⊑ α k)) p comp1)

              right-neq2 : (Σ x ꞉ ⟨ 𝓔 ⟩ , (α i1) ＝ (inr x)) -> ((α j1) ＝ (inl y)) -> Σ k ꞉ I , (α i1 ⊑ α k) × (α j1 ⊑ α k) -> 𝟘
              right-neq2 p q (k , (comp1 , comp2)) = cases (case2 p k comp1) (case1 q k comp2) (split k)

          rightcase : (i1 : I) -> (Σ x ꞉ ⟨ 𝓔 ⟩ , (α i1) ＝ (inr x)) -> (has-sup _⊑_ α)
          rightcase i1 p = (inr (∐ 𝓔 d) , transport (λ z → is-sup _⊑_ (inr (∐ 𝓔 d)) z) eq (inr-is-continuous I b d))
            where
              b : I -> ⟨ 𝓔 ⟩
              b = right (right-neq i1 p)

              eq2 : (inr ∘ b) ∼ α
              eq2 = (right-eq (right-neq i1 p))
              
              eq : (inr ∘ b) ＝ α
              eq = (dfunext fe) eq2
              
              d : is-Directed 𝓔 b
              d = (∣_∣ i1 , λ i j → ∥∥-functor (λ (k , (p1 , p2)) → k , (lower (transport (λ z → inr (b i) ⊑ z) ((eq2 k)⁻¹) (transport (λ z → z ⊑ (α k)) ((eq2 i)⁻¹) p1)) , lower (transport (λ z → inr (b j) ⊑ z) ((eq2 k)⁻¹) (transport (λ z → z ⊑ (α k)) ((eq2 j)⁻¹) p2)))) (semi i j))





N-dcpo : DCPO {𝓤₀} {𝓤₀}
N-dcpo = ℕ , (_≤ℕ_ , ({!!} , ≤-is-prop-valued , ≤-refl , ≤-trans , ≤-anti) , {!!})


𝓛-functor : {X Y : 𝓤 ̇} -> (X -> Y) -> (𝓛 X) -> (𝓛 Y)
𝓛-functor f (P , φ , i) = P , f ∘ φ , i

𝓛-func-dcpo : {𝓓 𝓔 : DCPO {𝓤} {𝓣}} -> DCPO[ 𝓓 , 𝓔 ] -> DCPO[ (freely-add-⊥.𝓛-DCPO 𝓓) , (freely-add-⊥.𝓛-DCPO 𝓔) ]
𝓛-func-dcpo (f , cf) = 𝓛-functor f , {!!}
  where
    mf2 : (𝓓 𝓔 : DCPO {𝓤} {𝓣}) -> ((g , cg) : DCPO[ 𝓓 , 𝓔 ]) -> is-monotone (freely-add-⊥.𝓛-DCPO 𝓓) (freely-add-⊥.𝓛-DCPO 𝓔) (𝓛-functor g)
    mf2 𝓓 𝓔 (g , cg) = λ (_ , φ , _) (_ , ψ , _) (h , k) -> h , λ p → mf (φ p) (ψ (h p)) (k p)
      where
        mf : is-monotone 𝓓 𝓔 g
        mf = monotone-if-continuous 𝓓 𝓔 (g , cg)


𝓓 : ℕ → DCPO {𝓤₁} {𝓤₁}
𝓓 zero = 𝓛-DCPO {𝓤₀} {𝟘{𝓤₀}} (props-are-sets 𝟘-is-prop)
𝓓 (succ n) = freely-add-⊥.𝓛-DCPO (+-DCPO N-dcpo (𝓓 n ⟹ᵈᶜᵖᵒ freely-add-⊥.𝓛-DCPO (𝓓 n)))

𝓓-diagram : (n : ℕ)
          → DCPO[ 𝓓 n , 𝓓 (succ n) ]
          × DCPO[ 𝓓 (succ n) , 𝓓 n ]
𝓓-diagram zero = ((λ x → 𝟘 , 𝟘-elim , 𝟘-is-prop) , constant-functions-are-continuous (𝓓 0) (𝓓 1))
                 , ((λ x → 𝟘 , 𝟘-elim , 𝟘-is-prop) , constant-functions-are-continuous (𝓓 1) (𝓓 0))
𝓓-diagram (succ n) = (e , {!!}) , ({!!} , {!!})
  where
    en : DCPO[ 𝓓 n , 𝓓 (succ n) ]
    en = pr₁ (𝓓-diagram n)
    pn : DCPO[ 𝓓 (succ n) , 𝓓 n ]
    pn = pr₂ (𝓓-diagram n)
    e : ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 (succ (succ n)) ⟩
    e = 𝓛-functor (dep-cases (λ x → inl x)
                   (λ f → inr (DCPO-∘₃ (𝓓 (succ n)) (𝓓 n) (freely-add-⊥.𝓛-DCPO (𝓓 n)) (freely-add-⊥.𝓛-DCPO (𝓓 (succ n))) pn f (𝓛-func-dcpo en))))

{-DCPO-∘₃ (𝓓 (succ n)) (𝓓 n) (𝓓 n) (𝓓 (succ n)) (pr₂ (𝓓-diagram n)) f (pr₁ (𝓓-diagram n))-}

{-(e , e-continuity) , (p , p-continuity)-}





          

\end{code}
