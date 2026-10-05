/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Entropy
import AlgebraicComplexity.Probability.Pushforward

/-!
# Basic reindexing of finite probability laws

Finite tensor alphabets are frequently replaced by equivalent product alphabets, support
subtypes, or oriented copies.  This module proves that reindexing a `ProbabilityVector` commutes
with deterministic pushforward and preserves Shannon entropy.

The three-feature maximum-entropy adapter remains in the compatibility module
`Probability/Reindex.lean`.  Clients that only relabel laws or mapped-coordinate fibers should
import this lightweight module directly.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w x y

namespace ProbabilityVector

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- Relabelling a finite probability law along an equivalence preserves Shannon entropy.

Proof sketch: after unfolding entropy, the summand at `j` is the old summand at `e.symm j`;
finite summation along an equivalence is invariant. -/
@[simp] theorem entropy_reindex (e : I ≃ J) (p : ProbabilityVector I) :
    (p.reindex e).entropy = p.entropy := by
  unfold entropy
  exact e.symm.sum_comp (fun i ↦ Real.negMulLog (p.weight i))

/-- Relabelling preserves base-two Shannon entropy. -/
@[simp] theorem entropyBits_reindex (e : I ≃ J) (p : ProbabilityVector I) :
    (p.reindex e).entropyBits = p.entropyBits := by
  unfold entropyBits
  rw [entropy_reindex]

/-- Reindexing by an equivalence agrees with deterministic pushforward along that equivalence. -/
theorem reindex_eq_pushforward [DecidableEq J]
    (e : I ≃ J) (p : ProbabilityVector I) :
    p.reindex e = p.pushforward e := by
  classical
  apply ProbabilityVector.ext
  funext j
  rw [reindex_weight, pushforward_weight]
  rw [Finset.sum_eq_single (e.symm j)]
  · simp
  · intro i _ hi
    simp only [ite_eq_right_iff]
    intro hei
    exact (hi (e.injective (by simpa using hei))).elim
  · simp

/-- A deterministic statistic applied after relabelling is the original statistic composed with
the relabelling equivalence. -/
theorem pushforward_reindex
    {A : Type w} [Fintype A] [DecidableEq A]
    (f : J → A) (e : I ≃ J) (p : ProbabilityVector I) :
    (p.reindex e).pushforward f = p.pushforward (f ∘ e) := by
  classical
  rw [reindex_eq_pushforward, pushforward_comp]

/-- Relabelling the output of a deterministic statistic by an equivalence does not change the
entropy of its law. -/
theorem entropy_pushforward_equiv
    {A : Type w} {B : Type x} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : I → A) (e : A ≃ B) (p : ProbabilityVector I) :
    (p.pushforward (e ∘ f)).entropy = (p.pushforward f).entropy := by
  rw [← pushforward_comp e f p, ← reindex_eq_pushforward]
  exact entropy_reindex e (p.pushforward f)

/-- Base-two entropy is invariant when a deterministic statistic is relabelled by an
equivalence. -/
theorem entropyBits_pushforward_equiv
    {A : Type w} {B : Type x} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : I → A) (e : A ≃ B) (p : ProbabilityVector I) :
    (p.pushforward (e ∘ f)).entropyBits = (p.pushforward f).entropyBits := by
  unfold entropyBits
  rw [entropy_pushforward_equiv]

/-- Reindexing along an equivalence and then along its inverse recovers the original law. -/
@[simp] theorem reindex_symm_reindex (e : I ≃ J) (p : ProbabilityVector I) :
    (p.reindex e).reindex e.symm = p := by
  apply ProbabilityVector.ext
  funext i
  simp

/-- Reindexing first along an inverse and then along the equivalence recovers the original law. -/
@[simp] theorem reindex_reindex_symm (e : I ≃ J) (p : ProbabilityVector J) :
    (p.reindex e.symm).reindex e = p := by
  apply ProbabilityVector.ext
  funext j
  simp

end ProbabilityVector

end AlgebraicComplexity

