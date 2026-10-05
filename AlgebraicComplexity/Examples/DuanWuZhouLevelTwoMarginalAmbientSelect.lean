/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarginalAmbientFamily

/-!
# `hselect` at the marginal-typical ambient

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoMarginalAmbientFamily.lean`
cuts the six-orientation positive power down to the marginal-typical subpartition
`dwz63MarginalTypicalPower` (a legwise `select`, hence projection-closed and a genuine
restriction), and separately defines the word family `dwz63MarginalWords` that the hashing engine
takes as its ambient.  This module joins the two.

## The seam

The partition-level cut `dwz63MarginalKeep` and the word-level cut `Dwz63MarginalTypical` are the
same predicate read through `positiveWordEquiv`: `PartitionHashEncoding.supportWordAddress`
transposes a word of block addresses into a block address of words, and
`positiveWordEquiv_supportWordAddress` says reading leg `c` then position `j` agrees with reading
position `j` then leg `c`.  `dwz63MarginalTypicalPower_support` is the resulting identity

`(dwz63MarginalTypicalPower K n t).support = modeledAddresses n (legalTargets n (dwz63MarginalWords K n t))`,

which is exactly the `hsupport` premise of the *parametric*
`Tensor.Restricts.modeledTargets_to_markedXYIsolated`.  The hardcoded
`restricts_positivePower_to_markedXYIsolated` is at `Finset.univ` and is deliberately not used.

## What this buys

`dwz63_restricts_positivePower_jointRetainedMarginal` composes the marginal cut with the hash and
gives `hselect` from the full six-orientation power onto the retained family, at the ambient where
the leg fiber is `N_triple / N_X` rather than `∏_o (5 - d_o)`.  With
`exists_seed_dwz63JointRetainedMarginal` and `dwz63_x_injOn_jointRetainedMarginal` the three
hashing premises are then all available at the new ambient.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## The two readings of the marginal cut agree -/

/-- **Transposing the word does not move the marginal condition.**  The `c`-leg word of
`supportWordAddress` reads, at position `j`, exactly the `c` component of the `j`-th letter. -/
theorem dwz63MarginalKeep_supportWordAddress (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) (c : Leg) :
    dwz63MarginalKeep n t c (PartitionHashEncoding.supportWordAddress n q c) ↔
      ∀ o : Fin 6,
        WordType.multiplicity
            (fun j ↦ dwz63SymSixDigit o ((positiveWordEquiv _ n q j).val c)) =
          WordType.proportionalCounts (dwz63LegMarginal c) t := by
  have h : (positiveWordEquiv (DwzSymSixBlock Leg.X) n)
        (PartitionHashEncoding.supportWordAddress n q c) =
      fun j ↦ ((positiveWordEquiv ((dwz63SymSixPartition K).support) n) q j).val c :=
    PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun c ↦ DwzSymSixBlock c) (support := (dwz63SymSixPartition K).support) n q c
  simp only [dwz63MarginalKeep, h]

/-- **The word-level family is cut out by the legwise predicate.**  This is the `hkeep` premise of
`PartitionHashEncoding.filter_modeledLegalTargets_eq_of_mem_iff`. -/
theorem mem_dwz63MarginalWords_iff_keep (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) :
    q ∈ dwz63MarginalWords K n t ↔
      ∀ c : Leg, dwz63MarginalKeep n t c (PartitionHashEncoding.supportWordAddress n q c) := by
  rw [mem_dwz63MarginalWords]
  constructor
  · intro h c
    exact (dwz63MarginalKeep_supportWordAddress K n t q c).mpr fun o ↦ h c o
  · intro h c o
    exact (dwz63MarginalKeep_supportWordAddress K n t q c).mp (h c) o

section Seam

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-- **The seam.**  The marginal-typical subpartition's support is the modeled legal-target family
of the marginal-typical *words* --- the partition-level cut and the word-level cut agree.  This is
the `hsupport` premise the parametric extraction theorem consumes. -/
theorem dwz63MarginalTypicalPower_support (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n t : ℕ) :
    (dwz63MarginalTypicalPower K n t).support =
      (dwz63SymSixHashEncoding K R hp).modeledAddresses n
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63MarginalWords K n t)) := by
  classical
  refine Eq.trans ?_
    ((dwz63SymSixHashEncoding K R hp).filter_modeledLegalTargets_eq_of_mem_iff
      n (dwz63MarginalWords K n t) (dwz63MarginalKeep n t) (mem_dwz63MarginalWords_iff_keep K n t))
  rw [← (dwz63SymSixHashEncoding K R hp).positivePower_support_eq_modeledLegalTargets
    (dwz63SymSixPartition K) n]
  ext s
  simp [dwz63MarginalTypicalPower, PartitionedTensor.mem_select_support]

/-! ## `hselect` at the new ambient -/

/-- **`hselect`, from the marginal-typical subpartition.**  The parametric
`Tensor.Restricts.modeledTargets_to_markedXYIsolated` at `ambientWords := dwz63MarginalWords`. -/
theorem dwz63_restricts_marginalTypicalPower_jointRetainedMarginal [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (hmarked : markedWords ⊆ dwz63MarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts (dwz63MarginalTypicalPower K n t).realize
      ((dwz63MarginalTypicalPower K n t).withSupport
        (dwz63JointRetainedSupportMarginal K hp n t markedWords B seed)).realize :=
  Tensor.Restricts.modeledTargets_to_markedXYIsolated
    (dwz63SymSixHashEncoding K R hp) (dwz63MarginalWords K n t) markedWords hmarked B hB seed
    (dwz63MarginalTypicalPower K n t) (dwz63MarginalTypicalPower_support K hp n t)

/-- **`hselect` from the full six-orientation power.**  The marginal cut composed with the hash:
the whole point of the exercise, since the leg fiber is now measured against the marginal-typical
family rather than `Finset.univ`. -/
theorem dwz63_restricts_positivePower_jointRetainedMarginal [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (hmarked : markedWords ⊆ dwz63MarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts ((dwz63SymSixPartition K).positivePower n).realize
      ((dwz63MarginalTypicalPower K n t).withSupport
        (dwz63JointRetainedSupportMarginal K hp n t markedWords B seed)).realize :=
  (dwz63_restricts_positivePower_marginalTypical K n t).trans
    (dwz63_restricts_marginalTypicalPower_jointRetainedMarginal K hp n t markedWords hmarked B hB
      seed)

end Seam

end AlgebraicComplexity.Examples
