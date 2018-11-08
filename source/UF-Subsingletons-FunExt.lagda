In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-LeftCancellable

Π-is-prop : funext U V → {X : U ̇} {A : X → V ̇}
          → ((x : X) → is-prop (A x)) → is-prop (Π A)
Π-is-prop fe i f g = dfunext fe (λ x → i x (f x) (g x))

Π-is-singleton : funext U V → {X : U ̇} {A : X → V ̇}
               → ((x : X) → is-singleton (A x)) → is-singleton (Π A)
Π-is-singleton fe i = (λ x → pr₁ (i x)) , (λ f → dfunext fe (λ x → pr₂ (i x) (f x)))

is-prop-is-prop : {X : U ̇} → funext U U → is-prop (is-prop X)
is-prop-is-prop {U} {X} fe f g = c₁
 where
  l : is-set X
  l = prop-is-set f
  c : (x y : X) → f x y ≡ g x y
  c x y = l (f x y) (g x y)
  c₀ : (x : X) → f x ≡ g x
  c₀ x = dfunext fe (c x)
  c₁ : f ≡ g
  c₁  = dfunext fe c₀

equal-to-prop-is-prop : propext U → funext U U
                      → (P : U ̇) → is-prop P
                      → (X : U ̇) → is-prop (X ≡ P)
equal-to-prop-is-prop {U} pe fe P i = local-hedberg' P (λ X → g X ∘ f X , k X)
 where
  f : (X : U ̇) → X ≡ P → is-prop X × (X ⇔ P)
  f X refl = i , (id , id)
  g : (X : U ̇) → is-prop X × (X ⇔ P) → X ≡ P
  g X (l , φ , γ) = pe l i φ γ
  j : (X : U ̇) → is-prop (is-prop X × (X ⇔ P))
  j X = ×-prop-criterion ((λ _ → is-prop-is-prop fe) ,
                          (λ l → ×-is-prop (Π-is-prop fe (λ x → i))
                                            (Π-is-prop fe (λ p → l))))
  k : (X : U ̇) → constant (g X ∘ f X)
  k X p q = ap (g X) (j X (f X p) (f X q))

is-prop-is-singleton : {X : U ̇} → funext U U → is-prop(is-singleton X)
is-prop-is-singleton {U} {X} fe (x , φ) (y , γ) = to-Σ-≡ (φ y , dfunext fe λ z → iss {y} {z} _ _)
 where
  isp : is-prop X
  isp = is-singleton-is-prop (y , γ)
  iss : is-set X
  iss = prop-is-set isp

Π-is-set : funext U V → {X : U ̇} {A : X → V ̇}
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set {U} {V} fe {X} {A} isa {f} {g} = b
 where
  a : is-prop (f ∼ g)
  a p q = dfunext fe λ x → isa x (p x) (q x)
  b : is-prop(f ≡ g)
  b = left-cancellable-reflects-is-prop happly (section-lc happly (pr₂ (fe f g))) a

\end{code}

The meat of the following proof is is-prop-is-set'. The rest of the
code is to deal with implicit arguments in conjunction with function
extensionality. The solution is not ideal. Ideally, functions with
implicit parameters should be the same as their versions with explicit
parameters.

\begin{code}

is-prop-is-set : {X : U ̇} → funext U U → is-prop (is-set X)
is-prop-is-set {U} {X} fe = h
 where
  is-set' : U ̇ → U ̇
  is-set' X = (x y : X) → is-prop(x ≡ y)

  is-prop-is-set' : {X : U ̇} → funext U U → is-prop (is-set' X)
  is-prop-is-set' fe = Π-is-prop fe
                         (λ x → Π-is-prop fe
                         (λ y → is-prop-is-prop fe))

  f : {X : U ̇} → is-set' X → is-set X
  f s {x} {y} = s x y

  g : {X : U ̇} → is-set X → is-set' X
  g s x y = s {x} {y}

  h : is-prop (is-set X)
  h = subtype-of-prop-is-prop g (ap f) (is-prop-is-set' fe)

\end{code}

\begin{code}

decidable-is-prop : {P : U ̇} → funext U U₀ → is-prop P → is-prop(P + ¬ P)
decidable-is-prop fe₀ isp = sum-of-contradictory-props
                             isp
                             (Π-is-prop fe₀ λ _ → 𝟘-is-prop)
                             (λ p u → u p)

PropExt : funext U U → propext U → {p q : Ω U}
        → (p holds → q holds) → (q holds → p holds) → p ≡ q
PropExt {U} fe pe {p} {q} f g =
 to-Σ-≡ ((pe (holds-is-prop p) (holds-is-prop q) f g) , is-prop-is-prop fe _ _)

Ω-is-set : funext U U → propext U → is-set (Ω U)
Ω-is-set {U} fe pe = identification-collapsible-is-set pc
 where
  A : (p q : Ω U) → U ̇
  A p q = (p holds → q holds) × (q holds → p holds)
  A-is-prop : (p q : Ω U) → is-prop(A p q)
  A-is-prop p q = Σ-is-prop (Π-is-prop fe
                                   (λ _ → holds-is-prop q))
                                   (λ _ → Π-is-prop fe (λ _ → holds-is-prop p))
  g : (p q : Ω U) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (a ⁻¹)
  h  : (p q : Ω U) → A p q → p ≡ q
  h p q (u , v) = PropExt fe pe u v
  f  : (p q : Ω U) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  constant-f : (p q : Ω U) (d e : p ≡ q) → f p q d ≡ f p q e
  constant-f p q d e = ap (h p q) (A-is-prop p q (g p q d) (g p q e))
  pc : {p q : Ω U} → Σ \(f : p ≡ q → p ≡ q) → constant f
  pc {p} {q} = (f p q , constant-f p q)

powerset-is-set : {A : U ̇} → funext U (V ⁺) → funext V V → propext V
                → is-set (A → Ω V)
powerset-is-set {U} fe fe' pe = Π-is-set fe (λ x → Ω-is-set fe' pe)

neg-is-prop : {X : U ̇} → funext U U₀ → is-prop(¬ X)
neg-is-prop fe = Π-is-prop fe (λ x → 𝟘-is-prop)

not : funext U U₀ → Ω U → Ω U
not fe (P , i) = (¬ P , neg-is-prop fe)

\end{code}

For the moment we work with U₀ here because 𝟙 and ⊤ live in U₀:

\begin{code}

equal-⊤-is-true : (P : U ̇) (i : is-prop P)
               → (P , i) ≡ ⊤ → P
equal-⊤-is-true P hp r = f *
 where
  s : 𝟙 ≡ P
  s = (ap pr₁ r)⁻¹
  f : 𝟙 → P
  f = transport id s

true-is-equal-⊤ : propext U → funext U U → (P : U ̇) (i : is-prop P)
                → P → (P , i) ≡ ⊤
true-is-equal-⊤ pe fe P i x = to-Σ-≡ (pe i 𝟙-is-prop unique-to-𝟙 (λ _ → x) ,
                                        is-prop-is-prop fe _ _)

Ω-ext : propext U → funext U U → {p q : Ω U}
      → (p ≡ ⊤ → q ≡ ⊤) → (q ≡ ⊤ → p ≡ ⊤) → p ≡ q
Ω-ext pe fe {(P , i)} {(Q , j)} f g = to-Σ-≡ (pe i j I II ,
                                              is-prop-is-prop fe _ _ )
 where
  I : P → Q
  I x = equal-⊤-is-true Q j (f (true-is-equal-⊤ pe fe P i x))
  II : Q → P
  II y = equal-⊤-is-true P i (g (true-is-equal-⊤ pe fe Q j y))

\end{code}

Without excluded middle, we have that:

\begin{code}

no-truth-values-other-than-⊥-or-⊤ : funext U U → propext U
                                   → ¬ Σ \(p : Ω U) → (p ≢ ⊥) × (p ≢ ⊤)
no-truth-values-other-than-⊥-or-⊤ fe pe ((P , isp) , (f , g)) = φ u
 where
   u : ¬ P
   u p = g l
     where
       l : (P , isp) ≡ ⊤
       l = PropExt fe pe unique-to-𝟙 (λ _ → p)
   φ : ¬¬ P
   φ u = f l
     where
       l : (P , isp) ≡ ⊥
       l = PropExt fe pe (λ p → 𝟘-elim (u p)) unique-from-𝟘

\end{code}

The above and following 𝟘-elim is used to coerce from 𝟘 {U} to 𝟘 {U₀}
as this is where negations take values in.

\begin{code}

⊥-is-not-⊤ : ¬(⊥ {U} ≡ ⊤ {U})
⊥-is-not-⊤ b = 𝟘-elim(𝟘-is-not-𝟙 (ap _holds b))

\end{code}
