The Cantor-Schröder-Bernstein for homotopy types, or ∞-groupoids, in Agda
-------------------------------------------------------------------------

Martin Escardo, 22nd and 24th January 2020, with further additions
after that.

This file needs the Agda release candidate 2.6.1.

There are two parts, which assume function extensionality but not
univalence or the existence of propositional truncations (any
assumption beyond MLTT is explicit in each claim).


(1) A univalent-foundations version of Pierre Pradic and Chad
    E. Brown's argument that Cantor-Schröder-Bernstein implies
    excluded middle in constructive set theory. (Added 22nd January.)
    (https://arxiv.org/abs/1904.09193).

    Their proof, reproduced here, uses the compactness (also known as
    the searchability or omniscience) of ℕ∞.

    (See also Appendix II.)


(2) A proof that excluded middle implies Cantor-Schröder-Bernstein for
    all homotopy types, or ∞-groupoids. (Added 24th January.)

    For any pair of types, if each one is embedded into the other,
    then they are equivalent.

    For this it is crucial that a map is an embedding if and only if
    its fibers are all propositions (rather than merely the map being
    left-cancellable).

    As far as we know, (2) is a new result.

    This part is the Agda version of https://arxiv.org/abs/2002.07079.
    Check our lecture notes to learn HoTT/UF with Agda:
    https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/ if

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module CantorSchroederBernstein where

open import SpartanMLTT
open import CompactTypes
open import ConvergentSequenceCompact
open import DecidableAndDetachable
open import DiscreteAndSeparated
open import GenericConvergentSequence
open import NaturalNumbers-Properties
open import Plus-Properties
open import UF-Base
open import UF-Equiv
open import UF-Embeddings
open import UF-ExcludedMiddle
open import UF-FunExt
open import UF-Miscelanea
open import UF-PropTrunc
open import UF-Retracts
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

\end{code}

Our formulation of Cantor-Schröder-Bernstein:

\begin{code}

CSB : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
CSB X Y = (X ↪ Y) × (Y ↪ X) → X ≃ Y

CantorSchröderBernstein : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
CantorSchröderBernstein 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → CSB X Y

\end{code}

Part 1
------

The following is Lemma 7 of the above reference, using retractions
rather than surjections, for simplicity:

\begin{code}

Pradic-Brown-lemma : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                   → retract (A + X) of X
                   → Compact X
                   → decidable A
Pradic-Brown-lemma {𝓤} {𝓥} {X} {A} (r , s , η) c = γ e
 where
  P : X → 𝓤 ⊔ 𝓥 ̇
  P x = Σ a ꞉ A , r x ≡ inl a

  d : (x : X) → decidable (P x)
  d x = equality-cases (r x)
         (λ (a : A) (u : r x ≡ inl a) → inl (a , u))
         (λ (y : X) (v : r x ≡ inr y) → inr (λ (a , u) → +disjoint (inl a ≡⟨ u ⁻¹ ⟩
                                                                    r x   ≡⟨ v    ⟩
                                                                    inr y ∎)))

  e : decidable (Σ x ꞉ X , P x)
  e = c P d

  f : A → Σ x ꞉ X , P x
  f a = s (inl a) , a , η (inl a)

  γ : decidable (Σ x ꞉ X , P x) → decidable A
  γ (inl (x , a , u)) = inl a
  γ (inr φ)           = inr (contrapositive f φ)

\end{code}

We formulate the following in more generality than we need
here. Recall that a point x is h-isolated if the identity type x ≡ y
is a subsingleton for every y.

\begin{code}

elemma' : {X : 𝓤 ̇ } {P : 𝓥 ̇ } (z : P → X) (s : X → X)
        → is-prop P
        → ((p : P) → is-h-isolated (z p))
        → disjoint-images z s
        → is-embedding s
        → (X ↪ P + X) × (P + X ↪ X)
elemma' {𝓤} {𝓥} {X} {P} z s i h d e = ((f , j) , (g , k))
 where
  f : X → P + X
  f = inr

  j : is-embedding f
  j = inr-is-embedding P X

  g : P + X → X
  g = cases z s

  l : is-embedding z
  l = maps-of-props-into-h-isolated-points-are-embeddings z i h

  k : is-embedding g
  k = disjoint-cases-embedding z s l e d

\end{code}

The level of generality we need here is the following. Recall that a
point is x isolated if equality x ≡ y is decidable for every y. By
Hedberg's Theorem, every isolated point is h-isolated.

\begin{code}

elemma : {X : 𝓤 ̇ } {P : 𝓥 ̇ } (x₀ : X) (s : X → X)
       → is-set X
       → is-prop P
       → is-isolated x₀
       → ((x : X) → x₀ ≢ s x)
       → left-cancellable s
       → (X ↪ P + X) × (P + X ↪ X)
elemma {𝓤} {𝓥} {X} {P} x₀ s j i k d' lc = elemma' z s i h d e
 where
  z : P → X
  z p = x₀
  h : (p : P) → is-h-isolated (z p)
  h p = isolated-is-h-isolated x₀ k
  d : disjoint-images z s
  d p = d'
  e : is-embedding s
  e = lc-maps-into-sets-are-embeddings s lc j

\end{code}

In the following, function extensionality is used to know that (1) ℕ∞
is a set, (2) its finite elements (in particular zero) are isolated,
(3) ℕ∞ is compact.

\begin{code}

CSB-gives-EM : funext 𝓤₀ 𝓤₀
             → (P : 𝓤 ̇ )
             → is-prop P
             → CSB ℕ∞ (P + ℕ∞)
             → P + ¬ P
CSB-gives-EM fe P i csb = γ
 where
  e : ℕ∞ ≃ P + ℕ∞
  e = csb (elemma Zero Succ (ℕ∞-is-set fe) i (finite-isolated fe zero) (λ x → Zero-not-Succ) Succ-lc)

  ρ : retract (P + ℕ∞) of ℕ∞
  ρ = equiv-retract-r e

  γ : P + ¬ P
  γ = Pradic-Brown-lemma ρ (ℕ∞-Compact fe)

\end{code}

Hence if we assume Cantor-Schröder-Bernstein for the first universe 𝓤₀
and an arbitrary universe 𝓥, as formulated above, then we get excluded
middle for propositions in the universe 𝓥:

\begin{code}

CantorSchröderBernstein-gives-EM : funext 𝓤₀ 𝓤₀
                                 → CantorSchröderBernstein 𝓤₀ 𝓥
                                 → EM 𝓥
CantorSchröderBernstein-gives-EM fe csb P i = CSB-gives-EM fe P i (csb ℕ∞ (P + ℕ∞))

\end{code}

We remark that if instead of requiring that we have a designated
equivalence, we required that there is an unspecified equivalence in
the formulation of Cantor-Schröder-Bernstein, we would still get
excluded middle, because P + ¬ P is a proposition if P is:

\begin{code}

module wCSB-still-gives-EM (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 wCSB : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 wCSB X Y = (X ↪ Y) × (Y ↪ X) → ∥ X ≃ Y ∥

 wCantorSchröderBernstein : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
 wCantorSchröderBernstein 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → wCSB X Y

 wCantorSchröderBernstein-gives-EM : funext 𝓤₀ 𝓤₀
                                   → funext 𝓥 𝓤₀
                                   → wCantorSchröderBernstein 𝓤₀ 𝓥
                                   → EM 𝓥
 wCantorSchröderBernstein-gives-EM fe₀ fe w P i = γ
  where
   s : ∥ ℕ∞ ≃ P + ℕ∞ ∥
   s = w ℕ∞ (P + ℕ∞) (elemma Zero Succ (ℕ∞-is-set fe₀) i (finite-isolated fe₀ zero) (λ x → Zero-not-Succ) Succ-lc)
   t : ℕ∞ ≃ P + ℕ∞ → P + ¬ P
   t e = Pradic-Brown-lemma (equiv-retract-r e) (ℕ∞-Compact fe₀)
   γ : P + ¬ P
   γ = ∥∥-rec (decidability-of-prop-is-prop fe i) t s

\end{code}

Part 2
------

The Cantor-Schröder-Bernstein Theorem holds for all homotopy types, or
∞-gropoids, in the presence of excluded middle. It is crucial here
that embeddings have subsingleton fibers, so that e.g. the function
is-g-point defined in the proof is property rather than data and hence
we can apply univalent excluded middle to it. It is also worth
remembering, for the sake of comparing the classical result for sets
with its generalization to ∞-groupoids, that a map of types that are
sets is an embedding if and only if it is left-cancellable.

Our proof adapts Halmos' proof in his book Naive Set Theory to our
more general situation.

For foundational reasons, we make clear which instances of function
extensionality and excluded middle are needed to conclude
Cantor-Schröder-Bernstein for arbitrary universes 𝓤 and 𝓥.

Added 28th January. To better understand this proof, you may consult the blog
post

  https://homotopytypetheory.org/2020/01/26/the-cantor-schroder-bernstein-theorem-for-∞-groupoids/

first. However, we have tried to make the proof understandable as we
can here, and hopefully it should be possible to read it without
reference to the blog post.

\begin{code}

EM-gives-CantorSchröderBernstein : funext 𝓤 (𝓤 ⊔ 𝓥)
                                 → funext (𝓤 ⊔ 𝓥) 𝓤₀
                                 → funext 𝓤₀ (𝓤 ⊔ 𝓥)
                                 → EM (𝓤 ⊔ 𝓥)
                                 → CantorSchröderBernstein 𝓤 𝓥
EM-gives-CantorSchröderBernstein {𝓤} {𝓥} fe fe₀ fe₁ excluded-middle X Y ((f , f-is-emb) , (g , g-is-emb)) =

  need X ≃ Y which-is-given-by 𝒽

 where

  remark-f : type-of (f , f-is-emb) ≡ (X ↪ Y)
  remark-f = by-assumption

  remark-g : type-of (g , g-is-emb) ≡ (Y ↪ X)
  remark-g = by-assumption

\end{code}

In order to define 𝒽 : X ≃ Y, we use a notion of g-point.

\begin{code}

  is-g-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  is-g-point x = (x₀ : X) (n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x → fiber g x₀

\end{code}

What is important for our purposes is that this is property rather
than data, using the fact that g is an embedding, which means that its
fibers are all propositions.

\begin{code}

  recall : (x : X) → fiber g x ≡ (Σ y ꞉ Y , g y ≡ x)
  recall _ = by-definition

  also-recall : is-embedding g ≡ ((x : X) → is-prop (fiber g x))
  also-recall = by-definition

\end{code}

We use the fact that propositions are closed under products, which
requires function extensionality:

\begin{code}

  being-g-point-is-a-prop : (x : X) → is-prop (is-g-point x)
  being-g-point-is-a-prop x =
   Π-is-prop fe  (λ (x₀ : X                   ) →
   Π-is-prop fe₁ (λ (n  : ℕ                   ) →
   Π-is-prop fe  (λ (p  : ((g ∘ f) ^ n) x₀ ≡ x) → need is-prop (fiber g x₀)
                                                  which-is-given-by (g-is-emb x₀))))
\end{code}

By construction, considering x₀ = x and n = 0, we have that g is
invertible at g-points, because, by definition, we have that
((g ∘ f) ^ 0) x ≡ x).

\begin{code}

  g-is-invertible-at-g-points : (x : X) (γ : is-g-point x) → fiber g x
  g-is-invertible-at-g-points x γ = γ x 0 (by-definition ∶ ((g ∘ f) ^ 0) x ≡ x)

\end{code}

The fiber point is given by the first projection of the fiber:

\begin{code}

  g⁻¹ : (x : X) → is-g-point x → Y
  g⁻¹ x γ = fiber-point g x (g-is-invertible-at-g-points x γ)

\end{code}

Because being a g-point is property, we can apply excluded middle to
it:

\begin{code}

  recall-the-notion-of-decidability : {𝓦 : Universe} {A : 𝓦 ̇ } → decidable A ≡ (A + ¬ A)
  recall-the-notion-of-decidability = by-definition

  δ : (x : X) → decidable (is-g-point x)
  δ x = excluded-middle (is-g-point x) (being-g-point-is-a-prop x)

\end{code}

The rest of the proof shows that the following function is an
equivalence:

\begin{code}

  h : X → Y
  h x = Cases (δ x)
         (γ ꞉   is-g-point x ↦ g⁻¹ x γ)
         (ν ꞉ ¬ is-g-point x ↦ f x)

\end{code}

For that purpose, it is enough to show that it is left-cancellable and
split-surjective.

To show that it is left-cancellable, we first show that g⁻¹ is a
two-sided inverse in its domain of definition.

That it is a right inverse follows from the definition of fiber, by
taking the fiber path, which is given by the second projection:

\begin{code}

  g⁻¹-is-rinv : (x : X) (γ : is-g-point x) → g (g⁻¹ x γ) ≡ x
  g⁻¹-is-rinv x γ = fiber-path g x (g-is-invertible-at-g-points x γ)

\end{code}

That it is a left inverse follows from the above and the fact that g,
being an embedding, is left-cancellable:

\begin{code}

  g⁻¹-is-linv : (y : Y) (γ : is-g-point (g y)) → g⁻¹ (g y) γ ≡ y
  g⁻¹-is-linv y γ = have (g (g⁻¹ (g y) γ) ≡⟨ g⁻¹-is-rinv (g y) γ ⟩
                          g y             ∎)
                    so-apply embeddings-are-left-cancellable g g-is-emb

\end{code}

We also need the following two facts to establish the
left-cancellability of h:

\begin{code}

  α : (x : X) → is-g-point (g (f x)) → is-g-point x
  α x γ = need is-g-point x
          which-is-given-by
           assume x₀ ∶ X                    and
           assume n  ∶ ℕ                    and
           assume p  ∶ ((g ∘ f) ^ n) x₀ ≡ x then
            (need fiber g x₀
             which-is-given-by
              have ap (g ∘ f) p ∶ ((g ∘ f) ^ (succ n)) x₀ ≡ g (f x)
              so-apply γ x₀ (succ n))

  f-g⁻¹-disjoint-images : (x x' : X)
                        → ¬ is-g-point x
                        → (γ : is-g-point x')
                        → f x ≢ g⁻¹ x' γ
  f-g⁻¹-disjoint-images x x' ν γ p = have p ∶ f x ≡ g⁻¹ x' γ
                                     so need contradiction
                                        which-is-given-by
                                         have γ ∶ is-g-point x'
                                         which-is-impossible-by (v ∶ ¬ is-g-point x')
   where
    q : g (f x) ≡ x'
    q = have p ∶ f x ≡ g⁻¹ x' γ
        so-use (g (f x)      ≡⟨ ap g p            ⟩
                g (g⁻¹ x' γ) ≡⟨ g⁻¹-is-rinv x' γ  ⟩
                x'           ∎)
    u : ¬ is-g-point (g (f x))
    u = have ν ∶ ¬ is-g-point x
        so-apply contrapositive (α x)
    v : ¬ is-g-point x'
    v = transport (- ↦ ¬ is-g-point -) q u

\end{code}

It is convenient to work with the following auxiliary function H and
prove properties of H and then specialize them to h:

\begin{code}

  H : (x : X) → decidable (is-g-point x) → Y
  H x d = Cases d
           (γ ꞉   is-g-point x ↦ g⁻¹ x γ)
           (ν ꞉ ¬ is-g-point x ↦ f x)

  notice-that : h ≡ x ↦ H x (δ x)
  notice-that = by-definition

  h-lc : left-cancellable h
  h-lc {x} {x'} = l (δ x) (δ x')
   where
    l : (d : decidable (is-g-point x)) (d' : decidable (is-g-point x')) → H x d ≡ H x' d' → x ≡ x'

    l (inl γ) (inl γ') p = have p ∶ g⁻¹ x γ ≡ g⁻¹ x' γ'
                           so (x             ≡⟨ (g⁻¹-is-rinv x γ)⁻¹ ⟩
                               g (g⁻¹ x γ)   ≡⟨ ap g p              ⟩
                               g (g⁻¹ x' γ') ≡⟨ g⁻¹-is-rinv x' γ'   ⟩
                               x'            ∎)

    l (inl γ) (inr ν') p = have p ∶ g⁻¹ x γ ≡ f x'
                           which-is-impossible-by (- ↦ f-g⁻¹-disjoint-images x' x ν' γ (- ⁻¹))

    l (inr ν) (inl γ') p = have p ∶ f x ≡ g⁻¹ x' γ'
                           which-is-impossible-by f-g⁻¹-disjoint-images x x' ν γ'

    l (inr ν) (inr ν') p = have p ∶ f x ≡ f x'
                           so-apply embeddings-are-left-cancellable f f-is-emb

\end{code}

Next we want to show that h is split surjective. For that purpose, we
define the notion of f-point, which is data rather than property (as
several x₀ and n are possible answers in general).

(In particular, excluded middle can't be applied to the type
f-point x, because excluded middle applies only to truth values.)

\begin{code}

  f-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  f-point x = Σ x₀ ꞉ X , (Σ n ꞉ ℕ , ((g ∘ f) ^ n) x₀ ≡ x) × ¬ fiber g x₀

\end{code}

What is important for our argument is that non-f-points are g-points:

\begin{code}

  non-f-point-is-g-point : (x : X) → ¬ f-point x → is-g-point x
  non-f-point-is-g-point x ν x₀ n p = need fiber g x₀ which-is-given-by
    (Cases (excluded-middle (fiber g x₀) (g-is-emb x₀))
      (σ ꞉   fiber g x₀ ↦ σ)
      (u ꞉ ¬ fiber g x₀ ↦ have (x₀ , (n , p) , u) ∶ f-point x
                          which-is-impossible-by (ν ∶ ¬ f-point x)))

\end{code}

We use the notion of f-point to prove the following, whose statement
doesn't refer to the notion of f-point.

\begin{code}

  claim : (y : Y) → ¬ is-g-point (g y) → Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
  claim y ν = v
   where
    i : ¬¬ f-point (g y)
    i = have ν ∶ ¬ is-g-point (g y)
        so-apply contrapositive (non-f-point-is-g-point (g y))

    ii : f-point (g y) → Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
    ii (x₀ , (0 , p) , u) = have p ∶ x₀ ≡ g y
                            so have (y , (p ⁻¹)) ∶ fiber g x₀
                               which-is-impossible-by (u ∶ ¬ fiber g x₀)
    ii (x₀ , (succ n , p) , u) = a , b
     where
      q : f (((g ∘ f) ^ n) x₀) ≡ y
      q = have p ∶ ((g ∘ f) ^ (succ n)) x₀  ≡ g y
                 ∶ g (f (((g ∘ f) ^ n) x₀)) ≡ g y
          so-apply embeddings-are-left-cancellable g g-is-emb
      a : fiber f y
      a = ((g ∘ f) ^ n) x₀ , q
      b : ¬ is-g-point (((g ∘ f) ^ n) x₀)
      b = assume γ ∶ is-g-point (((g ∘ f) ^ n) x₀)
          then (have γ x₀ n refl ∶ fiber g x₀
                which-is-impossible-by (u ∶ ¬ fiber g x₀))

    iii : ¬¬ (Σ (x , p) ꞉ fiber f y , ¬ is-g-point x)
    iii = double-contrapositive ii i

    iv : is-prop (Σ (x , p) ꞉ fiber f y , ¬ is-g-point x)
    iv = have f-is-emb y ∶ is-prop (fiber f y)
         so-apply subtype-of-prop-is-a-prop pr₁ (pr₁-lc (λ {σ} → negations-are-props fe₀))

    v : Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
    v = double-negation-elimination excluded-middle _ iv iii

\end{code}

With this we are ready to show that h is a split surjection. The idea
is that, given y : Y, we check whether g y is a g-point or not, and if
it is we map it to g y, and otherwise we map y to the point x : X
given by the above claim. But then, of course, we also need to argue
that this works. As above, we use the auxiliary function H for that
purpose.

\begin{code}
  h-split-surjection : (y : Y) → Σ x ꞉ X , h x ≡ y
  h-split-surjection y = x , p
   where
    a : decidable (is-g-point (g y)) → Σ x ꞉ X , ((d : decidable (is-g-point x)) → H x d ≡ y)
    a (inl γ) = g y , ψ
     where
      ψ : (d : decidable (is-g-point (g y))) → H (g y) d ≡ y
      ψ (inl γ') = H (g y) (inl γ') ≡⟨ by-definition    ⟩
                   g⁻¹ (g y) γ'     ≡⟨ g⁻¹-is-linv y γ' ⟩
                   y                ∎
      ψ (inr ν)  = have ν ∶ ¬ is-g-point (g y)
                   which-contradicts (γ ∶ is-g-point (g y))
    a (inr ν) = x , ψ
     where
      w : Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
      w = have ν ∶ ¬ is-g-point (g y)
          so-apply claim y
      x : X
      x = fiber-point f y (pr₁ w)
      p : f x ≡ y
      p = fiber-path f y (pr₁ w)
      ψ : (d : decidable (is-g-point x)) → H x d ≡ y
      ψ (inl γ) = have γ ∶ is-g-point x
                  which-is-impossible-by (pr₂ w ∶ ¬ is-g-point x)
      ψ (inr ν) = H x (inr ν) ≡⟨ by-definition ⟩
                  f x         ≡⟨ p             ⟩
                  y           ∎
    b : Σ x ꞉ X ,((d : decidable (is-g-point x)) → H x d ≡ y)
    b = a (δ (g y))
    x : X
    x = pr₁ b
    p : h x ≡ y
    p = h x       ≡⟨ by-construction ⟩
        H x (δ x) ≡⟨ pr₂ b (δ x)     ⟩
        y         ∎

\end{code}

And because left-cancellable split surjections are equivalences, we
are done:

\begin{code}

  𝒽 : X ≃ Y
  𝒽 = h , lc-split-surjections-are-equivs h h-lc h-split-surjection

\end{code}

We record the following special case:

\begin{code}

EM-gives-CantorSchröderBernstein₀ : funext 𝓤₀ 𝓤₀
                                  → EM 𝓤₀
                                  → CantorSchröderBernstein 𝓤₀ 𝓤₀
EM-gives-CantorSchröderBernstein₀ fe = EM-gives-CantorSchröderBernstein fe fe fe

\end{code}


APPENDIX I
----------

The above is an attempt to make the proof more readable and match the
blog post. Here is a more concise version of the above in a more
direct Agda style which some will prefer (and which could be made even
more concise by avoiding auxiliary definitions used for the purpose of
indicating types explicitly).

\begin{code}

EM-gives-CantorSchröderBernstein' : funext 𝓤 (𝓤 ⊔ 𝓥)
                                  → funext (𝓤 ⊔ 𝓥) 𝓤₀
                                  → funext 𝓤₀ (𝓤 ⊔ 𝓥)
                                  → EM (𝓤 ⊔ 𝓥)
                                  → CantorSchröderBernstein 𝓤 𝓥
EM-gives-CantorSchröderBernstein' {𝓤} {𝓥} fe fe₀ fe₁ excluded-middle X Y ((f , f-is-emb) , (g , g-is-emb)) = 𝒽
 where
  is-g-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  is-g-point x = (x₀ : X) (n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x → fiber g x₀

  g-is-invertible-at-g-points : (x : X) (γ : is-g-point x) → fiber g x
  g-is-invertible-at-g-points x γ = γ x 0 refl

  g⁻¹ : (x : X) → is-g-point x → Y
  g⁻¹ x γ = fiber-point g x (g-is-invertible-at-g-points x γ)

  g⁻¹-is-rinv : (x : X) (γ : is-g-point x) → g (g⁻¹ x γ) ≡ x
  g⁻¹-is-rinv x γ = fiber-path g x (g-is-invertible-at-g-points x γ)

  g⁻¹-is-linv : (y : Y) (γ : is-g-point (g y)) → g⁻¹ (g y) γ ≡ y
  g⁻¹-is-linv y γ = embeddings-are-left-cancellable g g-is-emb (g⁻¹-is-rinv (g y) γ)

  α : (x : X) → is-g-point (g (f x)) → is-g-point x
  α x γ x₀ n p = γ x₀ (succ n) (ap (g ∘ f) p)

  f-g⁻¹-disjoint-images : (x x' : X)
                        → ¬ is-g-point x
                        → (γ : is-g-point x')
                        → f x ≢ g⁻¹ x' γ
  f-g⁻¹-disjoint-images x x' ν γ p = 𝟘-elim (v γ)
   where
    q = g (f x)      ≡⟨ ap g p            ⟩
        g (g⁻¹ x' γ) ≡⟨ g⁻¹-is-rinv x' γ  ⟩
        x'           ∎
    u : ¬ is-g-point (g (f x))
    u = contrapositive (α x) ν
    v : ¬ is-g-point x'
    v = transport (λ - → ¬ is-g-point -) q u

  being-g-point-is-a-prop : (x : X) → is-prop (is-g-point x)
  being-g-point-is-a-prop x = Π-is-prop fe (λ x₀ → Π-is-prop fe₁ (λ _ → Π-is-prop fe (λ _ → g-is-emb x₀)))

  δ : (x : X) → decidable (is-g-point x)
  δ x = excluded-middle (is-g-point x) (being-g-point-is-a-prop x)

  H : (x : X) → decidable (is-g-point x) → Y
  H x (inl γ) = g⁻¹ x γ
  H x (inr _) = f x

  h : X → Y
  h x = H x (δ x)

  h-lc : left-cancellable h
  h-lc {x} {x'} = l (δ x) (δ x')
   where
    l : (d : decidable (is-g-point x)) (d' : decidable (is-g-point x')) → H x d ≡ H x' d' → x ≡ x'
    l (inl γ) (inl γ') p = x             ≡⟨ (g⁻¹-is-rinv x γ)⁻¹     ⟩
                           g (g⁻¹ x γ)   ≡⟨ ap g p                  ⟩
                           g (g⁻¹ x' γ') ≡⟨ g⁻¹-is-rinv x' γ'   ⟩
                           x'            ∎
    l (inl γ) (inr ν') p = 𝟘-elim(f-g⁻¹-disjoint-images x' x  ν' γ (p ⁻¹))
    l (inr ν) (inl γ') p = 𝟘-elim(f-g⁻¹-disjoint-images x  x' ν  γ' p)
    l (inr ν) (inr ν') p = embeddings-are-left-cancellable f f-is-emb p

  f-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  f-point x = Σ x₀ ꞉ X , (Σ n ꞉ ℕ , ((g ∘ f) ^ n) x₀ ≡ x) × ¬ fiber g x₀

  non-f-point-is-g-point : (x : X) → ¬ f-point x → is-g-point x
  non-f-point-is-g-point x ν x₀ n p =
   Cases (excluded-middle (fiber g x₀) (g-is-emb x₀))
    (λ (σ :   fiber g x₀) → σ)
    (λ (u : ¬ fiber g x₀) → 𝟘-elim(ν (x₀ , (n , p) , u)))

  claim : (y : Y) → ¬ is-g-point (g y) → Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
  claim y ν = v
   where
   i : ¬¬ f-point (g y)
   i = contrapositive (non-f-point-is-g-point (g y)) ν

   ii : f-point (g y) → Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
   ii (x₀ , (0      , p) , u) = 𝟘-elim (u (y , (p ⁻¹)))
   ii (x₀ , (succ n , p) , u) = a , b
    where
     q : f (((g ∘ f) ^ n) x₀) ≡ y
     q = embeddings-are-left-cancellable g g-is-emb p
     a : fiber f y
     a = ((g ∘ f) ^ n) x₀ , q
     b : ¬ is-g-point (((g ∘ f) ^ n) x₀)
     b γ = 𝟘-elim (u (γ x₀ n refl))

   iii : ¬¬ (Σ (x , p) ꞉ fiber f y , ¬ is-g-point x)
   iii = double-contrapositive ii i

   iv : is-prop (Σ (x , p) ꞉ fiber f y , ¬ is-g-point x)
   iv = subtype-of-prop-is-a-prop pr₁ (pr₁-lc (λ {σ} → negations-are-props fe₀)) (f-is-emb y)

   v : Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
   v = double-negation-elimination excluded-middle _ iv iii

  h-split-surjection : (y : Y) → Σ x ꞉ X , h x ≡ y
  h-split-surjection y = x , p
   where
    a : decidable (is-g-point (g y)) → Σ x ꞉ X , ((d : decidable (is-g-point x)) → H x d ≡ y)
    a (inl γ) = g y , ψ
     where
      ψ : (d : decidable (is-g-point (g y))) → H (g y) d ≡ y
      ψ (inl γ') = g⁻¹-is-linv y γ'
      ψ (inr ν)  = 𝟘-elim (ν γ)
    a (inr ν) = x , ψ
     where
      w : Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
      w = claim y ν
      x : X
      x = fiber-point f y (pr₁ w)
      ψ : (d : decidable (is-g-point x)) → H x d ≡ y
      ψ (inl γ) = 𝟘-elim (pr₂ w γ)
      ψ (inr ν) = fiber-path f y (pr₁ w)

    b : Σ x ꞉ X , ((d : decidable (is-g-point x)) → H x d ≡ y)
    b = a (δ (g y))
    x : X
    x = pr₁ b
    p : h x ≡ y
    p = h x       ≡⟨ by-construction ⟩
        H x (δ x) ≡⟨ pr₂ b (δ x)     ⟩
        y         ∎

  𝒽 : X ≃ Y
  𝒽 = h , lc-split-surjections-are-equivs h h-lc h-split-surjection

\end{code}

APPENDIX II
-----------

Added 17th Feb 2020 (a stronger result was added below, 18th Feb 2020).

Coming back to part 1, we consider what follows if we assume CSB for
types with decidable equality (which are necessarily sets) only. Such
types are called discrete. We adapt an argument in Johnstone's
Sketches of an Elephant Volume 2 (Lemma D.4.1.2).

See
https://www.sciencedirect.com/science/article/pii/S0019357718303276
for BKS⁺ (strong Brouwer-Kripke Schema) and the fact that together
with Markov Principle it implies excluded middle (attributed to
Moschovakis). The terminology "is-rosolini" is in connection with the
Rosolini dominance from synthetic domain theory and topology.

\begin{code}

is-rosolini : 𝓤 ̇ → 𝓤 ⁺ ̇
is-rosolini {𝓤} P = Σ A ꞉ (ℕ → 𝓤 ̇ ) , ((n : ℕ) → decidable (A n))
                                    × is-prop (Σ A)
                                    × (P ⇔ Σ A)

private
 observation : (A : ℕ → 𝓤 ̇ ) → is-prop (Σ A) → (n : ℕ) → is-prop (A n)
 observation A i n a a' = t
  where
   q : (n , a) ≡ (n , a')
   q = i (n , a) (n , a')
   t = a                        ≡⟨ refl                                                  ⟩
       transport A refl       a ≡⟨ ap (λ - → transport A - a) (ℕ-is-set refl (ap pr₁ q)) ⟩
       transport A (ap pr₁ q) a ≡⟨ from-Σ-≡' q                                           ⟩
       a'                       ∎

BKS⁺ : (𝓤 : Universe) → 𝓤 ⁺ ̇
BKS⁺ 𝓤 = (P : 𝓤 ̇ ) → is-prop P → is-rosolini P

\end{code}

It is convenient to work with the following formulation of Markov's
Principle that avoids ∃ (and hence propositional truncations), which
is easily seen to be equivalent to the traditional formulation using ∃
(using the fact that unique choice just holds (trivially) in HoTT/UF).

\begin{code}

MP : (𝓤 : Universe) → 𝓤 ⁺ ̇
MP 𝓤 = (A : ℕ → 𝓤 ̇ ) → ((n : ℕ) → decidable (A n)) → is-prop (Σ A) → ¬¬ Σ A → Σ A

\end{code}

The following, which derives double negation elimination from BKS⁺ and
MP, is formulated and proved in pure (spartan) MLTT:

\begin{code}

BKS⁺-and-MP-give-DNE : BKS⁺ 𝓤 → MP 𝓤 → DNE 𝓤
BKS⁺-and-MP-give-DNE {𝓤} bks mp P i = γ (bks P i)
 where
  γ : (Σ A ꞉ (ℕ → 𝓤 ̇ ) , ((n : ℕ) → decidable (A n)) × is-prop (Σ A) × (P ⇔ Σ A))
    → ¬¬ P → P
  γ (A , d , j , f , g) = dne
   where
    f' : ¬¬ P → ¬¬ Σ A
    f' = double-contrapositive f
    h : ¬¬ Σ A → Σ A
    h = mp A d j
    dne : ¬¬ P → P
    dne = g ∘ h ∘ f'

\end{code}

But the following, which derives excluded middle, needs function
extensionality:

\begin{code}

BKS⁺-and-MP-give-EM : funext 𝓤 𝓤₀ → BKS⁺ 𝓤 → MP 𝓤 → EM 𝓤
BKS⁺-and-MP-give-EM fe bks MP = DNE-gives-EM fe (BKS⁺-and-MP-give-DNE bks MP)

\end{code}

So BKS⁺ "almost" gives excluded middle in some sense.

We now show that CSB for discrete types gives BKS⁺:

\begin{code}

blemma : {P : 𝓤 ̇ } {X : 𝓥 ̇ }
       → is-set X
       → is-prop P
       → X ≃ P + X
       → Σ A ꞉ (X → 𝓤 ⊔ 𝓥 ̇ ) , ((x : X) → decidable (A x)) × is-prop (Σ A) × (P ⇔ Σ A)
blemma {𝓤} {𝓥 } {P} {X} j i (f , (s , η) , (r , ε)) = A , d , k , (φ , γ)
 where
  A : X → 𝓤 ⊔ 𝓥 ̇
  A x = Σ p ꞉ P , f x ≡ inl p

  d : (x : X) → decidable (A x)
  d x = equality-cases (f x)
         (λ (p : P) (u : f x ≡ inl p) → inl (p , u))
         (λ (y : X) (v : f x ≡ inr y) → inr (λ (a , u) → +disjoint (inl a ≡⟨ u ⁻¹ ⟩
                                                                    f x   ≡⟨ v    ⟩
                                                                    inr y ∎)))

  k : is-prop (Σ A)
  k (x , p , u) (x' , p' , u') = t
   where
    q : x ≡ x'
    q = equivs-are-lc f ((s , η) , (r , ε)) (f x    ≡⟨ u               ⟩
                                             inl p  ≡⟨ ap inl (i p p') ⟩
                                             inl p' ≡⟨ u' ⁻¹           ⟩
                                             f x'   ∎)
    t : x , p , u ≡ x' , p' , u'
    t = to-Σ-≡ (q , to-Σ-≡ (i _ p' , +-is-set P X (props-are-sets i) j _ u'))

  φ : P → Σ A
  φ p = s (inl p) , p , η (inl p)

  γ : Σ A → P
  γ (x , p , u) = p

rlemma : {P : 𝓤 ̇ }
       → is-prop P
       → ℕ ≃ P + ℕ
       → is-rosolini P
rlemma = blemma ℕ-is-set

discrete-CantorSchröderBernstein : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
discrete-CantorSchröderBernstein 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → is-discrete X → is-discrete Y → CSB X Y

dlemma : (P : 𝓥 ̇ )
       → discrete-CantorSchröderBernstein 𝓤₀ 𝓥
       → is-prop P → ℕ ≃ P + ℕ
dlemma P csb i = b
 where
  a : (ℕ ↪ P + ℕ) × (P + ℕ ↪ ℕ)
  a = elemma zero succ
       ℕ-is-set i
        (ℕ-is-discrete zero)
        (λ x (p : zero ≡ succ x) → positive-not-zero x (p ⁻¹))
        succ-lc
  b : ℕ ≃ P + ℕ
  b = csb ℕ (P + ℕ) ℕ-is-discrete (+discrete (props-are-discrete i) ℕ-is-discrete) a

discrete-CSB-gives-BKS⁺ : discrete-CantorSchröderBernstein 𝓤₀ 𝓥 → BKS⁺ 𝓥
discrete-CSB-gives-BKS⁺ csb P i = γ
 where
  e : ℕ ≃ P + ℕ
  e = dlemma P csb i

  γ : is-rosolini P
  γ = rlemma i e

\end{code}

Added 18th Feb 2020. We make the last development above sharper, at
the expense of assuming propositional extensionality (univalence for
propositions).

If we have a uniform way to get an equivalence ℕ ≃ P + ℕ for any
proposition P, given by a function

 φ : (P : 𝓤 ̇ ) → is-prop P → ℕ ≃ P + ℕ,

then we can use φ to decide P for any proposition P. The idea is to
first consider P=𝟙, and see which natural number n is mapped to inl *
by the equivalence f given by φ. Then, for an arbitrary proposition P,
if f maps n to inl p for some p, then P holds. Otherwise, if f maps n
to inl k for some k : ℕ, then P can't hold, for if it did we would
have p : P, and hence P=𝟙 by propositional extensionality, and f would
have to map n to inl p.

\begin{code}

ulemma : funext 𝓤 𝓤
       → propext 𝓤
       → ((P : 𝓤 ̇ ) → is-prop P → ℕ ≃ P + ℕ)
       → EM 𝓤
ulemma {𝓤} fe pe φ P i = γ
 where
  A : 𝓤 ⁺ ̇
  A = Σ Q ꞉ 𝓤 ̇ , is-prop Q × Q
  u : (Q : 𝓤 ̇ ) → is-prop (is-prop Q × Q)
  u Q (j , q) = ×-is-prop (being-a-prop-is-a-prop fe) j (j , q)
  v : is-prop A
  v (Q , j , q) (Q' , j' , q') = to-subtype-≡ u s
   where
    s : Q ≡ Q'
    s = pe j j' (λ _ → q') (λ _ → q)
  f : A → ℕ
  f (Q , j , q) = ⌜ ≃-sym (φ Q j) ⌝ (inl q)
  n : ℕ
  n = f (𝟙 , 𝟙-is-prop , *)
  g : (k : ℕ) (s : ⌜ φ P i ⌝ n ≡ inr k) → ¬ P
  g k s p = +disjoint' b
   where
    a : n ≡ f (P , i , p)
    a = ap f (v _ _)
    b = inr k                                 ≡⟨ s ⁻¹                          ⟩
        ⌜ φ P i ⌝ n                           ≡⟨ ap ⌜ φ P i ⌝ a                ⟩
        ⌜ φ P i ⌝ (f (P , i , p))             ≡⟨ refl                          ⟩
        ⌜ φ P i ⌝ (⌜ ≃-sym (φ P i) ⌝ (inl p)) ≡⟨ ≃-sym-is-rinv (φ P i) (inl p) ⟩
        inl p                                 ∎

  γ : P + ¬ P
  γ = equality-cases (⌜ φ P i ⌝ n)
       (λ (p : P) (r : ⌜ φ P i ⌝ n ≡ inl p) → inl p)
       (λ (k : ℕ) (s : ⌜ φ P i ⌝ n ≡ inr k) → inr (g k s))

discrete-CSB-gives-EM : funext 𝓥 𝓥
                      → propext 𝓥
                      → discrete-CantorSchröderBernstein 𝓤₀ 𝓥
                      → EM 𝓥
discrete-CSB-gives-EM {𝓥} fe pe csb = ulemma fe pe φ
 where
  φ : (P : 𝓥 ̇ ) → is-prop P → ℕ ≃ P + ℕ
  φ P = dlemma P csb

\end{code}

Thus, in particular, decidable equality is not enough to get a
constructive version of CSB. Even with decidable equality of the given
types, one still needs full excluded middle.

Discussion
----------

The Pradic-Brown argument, although it requires a non-discrete type to
work, has the advantage that if we weaken the statement of CSB to say
that an unspecified (rather than designated) equivalence exists, for
any two given embeddings in opposite directions,

    (X ↪ Y) × (Y ↪ X) → ∥ X ≃ Y ∥.

one still gets excluded middle, as already remarked above. And it is
is also nice and clear and short. Our argument, however, doesn't work
with this weakening, as in this case it is no longer possible to
define the function φ in the proof (without choice, which is stronger
than what we want to prove, namely excluded middle) to apply the
uniformity lemma. The reason is that Pradic and Brown use only one
instance of CSB, for a given proposition, whereas we use a family of
instances. In any case, in the other direction, excluded middle does
give CSB with a designated equivalence in the conclusion, as
previously shown above.
