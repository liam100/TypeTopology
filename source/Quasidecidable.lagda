Martin Escardo, 10th July 2020.

This file summarizes Quasidecidable-blackboard.lagda in a more
organized way. Only the main facts are included here.

We look at

  * Quasidecidable propositions (generalizing semidecidable propositions).

  * The initial σ-frame.

  * The free σ-sup-lattice on one generator.

Their definitions are given below verbally and in Agda.

We work in a spartan univalent type theory with Π, Σ, +, Id, 𝟘, 𝟙, ℕ,
perhaps W-types, propositional-truncation, univalence, universes. Most
of the time full univalence is not needed - propositional and
functional extenstionality suffice. Sometimes we also consider
propositional resizing, as an explicit assumption each time it is
used.

The above notions don't seem to be definable in our spartan univalent
type theory. Their specifications are as follows:

  * Quasidecidable propositions.

    They are the smallest set of propositions closed under 𝟘,𝟙, and
    countable existential quantification, or countable joins in the
    frame of propositions.

  * The initial σ-frame.

    A σ-frame has finite meets ⊤ and ∧ and countable joins ⋁, such
    that ∧ distributes over ⋁, with homomorphisms that preserve them.

  * The free σ-sup-lattice on one generator.

    A σ-sup-lattice has an empty join ⊥ and countable joins ⋁ with
    homomorphisms that preserve them. It automatically has binary
    joins, which are automatically preserved by homomorphisms.

We have:

 * Quasidecidable propositions exist (the precise definition of
   their existence is given below)  if and only if the free
   σ-sup-lattice on one generator exists.

   The quasidecidable propositions form a dominance.

 * The free σ-sup-lattice on one generator, if it exists, is also the
   initial σ-frame.

   We have that σ-sup-lattice homomorphisms from the free
   σ-sup-lattice on one generator into σ-Frame qua σ-sup-lattice
   automatically preserve finite meets and hence are σ-frame
   homomorphisms.

* Assuming that the free σ-sup-lattice on one generator exists, we
  have that σ-sup-lattices (and hence σ-Frames) have joins of families
  indexed by quasidecidable propositions.

  This means that they are algebras of the partiality monad induced by
  the dominance of quasipropositions (we haven't formalized this fact
  yet).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc
open import UF-FunExt
open import UF-Subsingletons

module Quasidecidable
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
        (pt  : propositional-truncations-exist)
       where

open import Quasidecidable-blackboard fe pe pt
open import UF-Size

import sigma-frame
import sigma-sup-lattice

\end{code}

The following three definitions are parametrized by a universe 𝓣,
which we may wish to be the first universe 𝓤₀, but the development is
universe independent.

The notion of existence of quasidecidable propositions, formulated as
a record:

\begin{code}

record quasidecidable-propositions-exist (𝓣 𝓚 : Universe) : 𝓤ω where
 open PropositionalTruncation pt
 field
  is-quasidecidable : 𝓣 ̇ → 𝓚 ̇

  being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P)

  𝟘-is-quasidecidable : is-quasidecidable 𝟘

  𝟙-is-quasidecidable : is-quasidecidable 𝟙

  quasidecidable-closed-under-ω-joins :
      (P : ℕ → 𝓣 ̇ )
    → ((n : ℕ) → is-quasidecidable (P n))
    → is-quasidecidable (∃ n ꞉ ℕ , P n)

  quasidecidable-induction : ∀ {𝓤}
      (F : 𝓣 ̇ → 𝓤 ̇ )
    → ((P : 𝓣 ̇ ) → is-prop (F P))
    → F 𝟘
    → F 𝟙
    → ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
    → (P : 𝓣 ̇ ) → is-quasidecidable P → F P
\end{code}

(It follows automatically that quasidecidable types are propositions.)

We also formulate the existence of the initial σ-frame as a record.

\begin{code}

record initial-σ-frame-exists (𝓣 : Universe) : 𝓤ω where
 open sigma-frame fe
 field
  𝓐 : σ-Frame 𝓣
  𝓐-is-initial : {𝓤 : Universe} (𝓑 : σ-Frame 𝓤) → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩), is-σ-frame-hom 𝓐 𝓑 f

\end{code}

And finally the existence of the free σ-sup-lattice on one generator:

\begin{code}

record free-σ-SupLat-on-one-generator-exists (𝓣 𝓚 : Universe) : 𝓤ω where
 open sigma-sup-lattice fe
 field
  𝓐 : σ-SupLat 𝓣 𝓚
  ⊤ : ⟨ 𝓐 ⟩
  𝓐-free : {𝓥 𝓦 : Universe} (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
         → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) , is-σ-suplat-hom 𝓐 𝓑 f
                                  × (f ⊤ ≡ t)
\end{code}

The main theorems are as follows, with the following conventions:

  * 𝓣 is the universe where the quasidecidable truth values live.

    Typically 𝓣 will be 𝓤₀ or 𝓤₁.

  * 𝓚 is the universe where the knowledge they are quasidecidable lives.

    Typically 𝓚 will be 𝓣 or 𝓣 ⁺

\begin{code}

variable 𝓚 : Universe

theorem₁ : quasidecidable-propositions-exist 𝓣 𝓚
         → free-σ-SupLat-on-one-generator-exists (𝓣 ⁺ ⊔ 𝓚) 𝓣
theorem₁ {𝓣} {𝓤} q = record {
                       𝓐 = QD ;
                       ⊤ = ⊤ ;
                       𝓐-free = QD-is-free-σ-SupLat
                       }
 where
  open quasidecidable-propositions-exist q
  open hypothetical-quasidecidability {𝓣} {𝓤}
        is-quasidecidable
        being-quasidecidable-is-prop
        𝟘-is-quasidecidable
        𝟙-is-quasidecidable
        quasidecidable-closed-under-ω-joins
        quasidecidable-induction

theorem₂ : free-σ-SupLat-on-one-generator-exists 𝓣 𝓤
         → quasidecidable-propositions-exist 𝓣 𝓣
theorem₂ {𝓣} {𝓤} f =
 record {
  is-quasidecidable = is-quasidecidable₀ ;
  being-quasidecidable-is-prop = being-quasidecidable₀-is-prop ;
  𝟘-is-quasidecidable = 𝟘-is-quasidecidable₀ ;
  𝟙-is-quasidecidable = 𝟙-is-quasidecidable₀ ;
  quasidecidable-closed-under-ω-joins = quasidecidable₀-closed-under-ω-joins ;
  quasidecidable-induction = quasidecidable₀-induction
  }

 where
  open free-σ-SupLat-on-one-generator-exists f
  open hypothetical-free-σ-SupLat-on-one-generator
  open assumption {𝓣} {𝓤} 𝓐 ⊤ 𝓐-free


theorem₃ : free-σ-SupLat-on-one-generator-exists 𝓣 𝓚
         → initial-σ-frame-exists 𝓣
theorem₃ {𝓣} {𝓚} f =
 record {
  𝓐 = 𝓐-qua-σ-frame ;
  𝓐-is-initial = 𝓐-qua-σ-frame-is-initial
  }
 where
  open free-σ-SupLat-on-one-generator-exists f
  open hypothetical-free-σ-SupLat-on-one-generator
  open assumption {𝓣} {𝓚} 𝓐 ⊤ 𝓐-free


theorem₄ : Propositional-Resizing
         → quasidecidable-propositions-exist 𝓣 𝓚
theorem₄ {𝓣} {𝓚} ρ =
 record {
  is-quasidecidable = is-quasidecidable ;
  being-quasidecidable-is-prop = being-quasidecidable-is-prop ;
  𝟘-is-quasidecidable = 𝟘-is-quasidecidable ;
  𝟙-is-quasidecidable = 𝟙-is-quasidecidable ;
  quasidecidable-closed-under-ω-joins = quasidecidable-closed-under-ω-joins ;
  quasidecidable-induction = quasidecidable-induction
  }

 where
  open quasidecidability-construction-from-resizing 𝓣 𝓚 ρ

\end{code}
