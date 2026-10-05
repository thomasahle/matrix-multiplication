/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ReindexBasic
import AlgebraicComplexity.Probability.TwoLetter

/-!
# Reindexing finite probability laws and marginal fibers

Finite alphabets in tensor arguments are routinely replaced by canonically equivalent product
alphabets, support subtypes, and oriented copies.  This file proves that such a relabelling changes
neither Shannon entropy nor maximum-entropy statements.

The basic `ProbabilityVector.reindex` construction and its entropy/pushforward laws live in
`Probability/ReindexBasic.lean`.  This compatibility layer adds transport of the reusable
`ThreeFeatureSystem` maximum-entropy interface.  These lemmas keep client proofs semantic: a
product law may be studied on an honest Cartesian product and then transported to the supported
tensor addresses through a proved equivalence.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w x y

/-! Basic probability-law reindexing is provided by `Probability/ReindexBasic.lean`. -/

namespace ThreeFeatureSystem

variable
    {S : Type u} {T : Type v} {C : Type w} {L : Type x} {R : Type y}
    [Fintype S] [Fintype T] [Fintype C] [Fintype L] [Fintype R]
    [DecidableEq C] [DecidableEq L] [DecidableEq R]

/-- Transport a three-feature system to an equivalent source alphabet. -/
def reindex (F : ThreeFeatureSystem S C L R) (e : S ≃ T) :
    ThreeFeatureSystem T C L R where
  coarse := F.coarse ∘ e.symm
  left := F.left ∘ e.symm
  right := F.right ∘ e.symm

/-- Relabelling both laws preserves membership in a three-feature marginal fiber. -/
theorem sameFiber_reindex
    (F : ThreeFeatureSystem S C L R) (e : S ≃ T)
    {p q : ProbabilityVector S} (h : F.SameFiber p q) :
    (F.reindex e).SameFiber (p.reindex e) (q.reindex e) := by
  constructor
  · change (p.reindex e).pushforward (F.coarse ∘ e.symm) =
      (q.reindex e).pushforward (F.coarse ∘ e.symm)
    rw [ProbabilityVector.pushforward_reindex,
      ProbabilityVector.pushforward_reindex]
    have hcomp : (F.coarse ∘ e.symm) ∘ e = F.coarse := by
      funext s
      simp
    simpa only [hcomp] using h.1
  constructor
  · change (p.reindex e).pushforward (F.left ∘ e.symm) =
      (q.reindex e).pushforward (F.left ∘ e.symm)
    rw [ProbabilityVector.pushforward_reindex,
      ProbabilityVector.pushforward_reindex]
    have hcomp : (F.left ∘ e.symm) ∘ e = F.left := by
      funext s
      simp
    simpa only [hcomp] using h.2.1
  · change (p.reindex e).pushforward (F.right ∘ e.symm) =
      (q.reindex e).pushforward (F.right ∘ e.symm)
    rw [ProbabilityVector.pushforward_reindex,
      ProbabilityVector.pushforward_reindex]
    have hcomp : (F.right ∘ e.symm) ∘ e = F.right := by
      funext s
      simp
    simpa only [hcomp] using h.2.2

/-- Maximum entropy in a three-feature fiber is invariant under relabelling its source alphabet.

Proof sketch: pull an arbitrary competitor back along `e.symm`.  Pushforward after reindexing is
pushforward along the transported feature, so the pulled law belongs to the original fiber.
Apply maximality there and use entropy invariance under equivalences on both sides. -/
theorem isMaximumEntropy_reindex
    (F : ThreeFeatureSystem S C L R) (e : S ≃ T)
    (p : ProbabilityVector S) (hp : F.IsMaximumEntropy p) :
    (F.reindex e).IsMaximumEntropy (p.reindex e) := by
  intro q hq
  have hfiber : F.SameFiber (q.reindex e.symm) p := by
    constructor
    · calc
        (q.reindex e.symm).pushforward F.coarse =
            q.pushforward (F.coarse ∘ e.symm) :=
          ProbabilityVector.pushforward_reindex F.coarse e.symm q
        _ = (p.reindex e).pushforward (F.coarse ∘ e.symm) := hq.1
        _ = p.pushforward F.coarse := by
          rw [ProbabilityVector.pushforward_reindex]
          congr 1
          funext s
          simp
    constructor
    · calc
        (q.reindex e.symm).pushforward F.left =
            q.pushforward (F.left ∘ e.symm) :=
          ProbabilityVector.pushforward_reindex F.left e.symm q
        _ = (p.reindex e).pushforward (F.left ∘ e.symm) := hq.2.1
        _ = p.pushforward F.left := by
          rw [ProbabilityVector.pushforward_reindex]
          congr 1
          funext s
          simp
    · calc
        (q.reindex e.symm).pushforward F.right =
            q.pushforward (F.right ∘ e.symm) :=
          ProbabilityVector.pushforward_reindex F.right e.symm q
        _ = (p.reindex e).pushforward (F.right ∘ e.symm) := hq.2.2
        _ = p.pushforward F.right := by
          rw [ProbabilityVector.pushforward_reindex]
          congr 1
          funext s
          simp
  have hentropy := hp (q.reindex e.symm) hfiber
  simpa using hentropy

end ThreeFeatureSystem

end AlgebraicComplexity
