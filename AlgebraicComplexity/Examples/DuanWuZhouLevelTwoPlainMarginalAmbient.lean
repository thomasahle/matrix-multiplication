/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLegMarginal
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareCounting
import AlgebraicComplexity.Tensor.PartitionedGroupingBoxes
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPartitionedPowerHashing

/-!
# The marginal-typical ambient at the plain fifteen-block partition

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` hashes a **plain power**:
`global_value.tex:12` bounds `V^(6)(𝒯)` for `𝒯 = (CW_q^{⊗2^{ℓ-1}})^{⊗n}`, and `sym₆` lives only
inside the value functional (`prelim.tex:142-146`, `def:value`).  So the object the hash acts on is
`(cwSquarePartitionedTensor K dwz63Q).positivePower n`, whose block labels are the fifteen coarse
Coppersmith--Winograd square addresses --- one component per position, one `X` leg with marginal
`dwz63AlphaX`, and no orientations anywhere.

This is the plain analogue of `Examples/DuanWuZhouLevelTwoMarginalAmbientFamily.lean`.  The
six-orientation reading machinery it carried --- source versus target conventions, the leg-source
multiset, the base-five digits --- was an artefact of hashing the `15 ^ 6`-block object and is
gone.  What is **not** an artefact, and is reproduced here unchanged, is the ambient-fiber
problem itself.

## The numbers, per position (nats)

Fixing an `X` letter `x` still leaves `5 - x` completions `(y, z)` with `y + z = 4 - x`, so over
`Finset.univ` the leg fiber of a marked triple is `Σ_x α_X(x)·ln(5 - x) = 1.2785727603610` ---
*identical* to the six-orientation figure --- against the sharp `H(α) - H(α_X) = 0.9240977007253`.
The deficit `0.3544750596357` would drop the retained rate to `0.7346993` where `H(α_X) =
1.0891744` is required.  Over the marginal-typical family the fiber is instead
`H(α') - H(α_X)` for `α'` the maximum-entropy member of `D_α`, which the committed
`dwz63_gibbsDeficit_le_log_hashLossMultiplier` caps at `H(α) - H(α_X) + log K`, so the retained
rate is at least `H(α_X) - log K = 1.0891743499950` --- the same expression as
`log dwz63TrueCopyRate`, with zero slack.

Here `D_α` is a set of distributions on the **fifteen cells**, which is exactly the domain the
Gibbs certificate is stated for; the six-orientation route needed the unstated extra step that a
maximum-entropy six-tuple distribution with per-orientation marginals factorises.

## Why a marginal cut and not a joint one

`Tensor/PartitionedExtraction.lean:36`'s `IsProjectionClosed` is the crossing-block condition, and
`PartitionedTensor.select_support_isProjectionClosed_univ`
(`Tensor/PartitionedGroupingBoxes.lean:60`) discharges it for every legwise `keep`.  A joint-type
cut fails it: take the `X` word of one typical address, the `Y` word of a second and the `Z` word
of a third; all three marginals are right, so the assembled address is ambient and each of its
labels is a selected label, yet its joint type need not be `α`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## Marginal typicality of a plain block word -/

/-- **Marginal typicality at the plain partition.**  Each leg's word carries the `dwz63Alpha`
marginal type at that leg.  One condition per leg, depending on that leg's word alone --- which is
what makes the cut a legwise `select`, hence projection-closed. -/
def Dwz63PlainMarginalTypical (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) : Prop :=
  ∀ c : Leg,
    WordType.multiplicity (fun j ↦ ((positiveWordEquiv _ n q j).val c)) =
      WordType.proportionalCounts (dwz63AlphaMarginal c) t

/-- **The marginal-typical word family**, the ambient the plain hash may legitimately run at. -/
noncomputable def dwz63PlainMarginalWords (K : Type u) [CommRing K] (n t : ℕ) :
    Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) := by
  classical
  exact Finset.univ.filter (Dwz63PlainMarginalTypical K n t)

theorem mem_dwz63PlainMarginalWords {K : Type u} [CommRing K] {n t : ℕ}
    {q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n} :
    q ∈ dwz63PlainMarginalWords K n t ↔ Dwz63PlainMarginalTypical K n t q := by
  classical
  simp [dwz63PlainMarginalWords]

/-! ## The cut, as a legwise `select` -/

/-- **The legwise keep predicate.**  At the plain partition a leg label is a single coarse degree,
so the condition is one word type per leg --- no digits and no orientations. -/
def dwz63PlainMarginalKeep (n t : ℕ) : ∀ _c : Leg, PositiveWord (Fin 5) n → Prop :=
  fun c word ↦
    WordType.multiplicity (positiveWordEquiv (Fin 5) n word) =
      WordType.proportionalCounts (dwz63AlphaMarginal c) t

/-- **The marginal-typical subpartition of the plain positive power.** -/
noncomputable def dwz63PlainMarginalTypicalPower (K : Type u) [CommRing K] (n t : ℕ) := by
  classical
  exact ((cwSquarePartitionedTensor K dwz63Q).positivePower n).select (dwz63PlainMarginalKeep n t)

/-- **The marginal cut is a restriction, with no hypothesis.**  This is the step a joint-type cut
cannot take. -/
theorem dwz63_restricts_positivePower_plainMarginalTypical (K : Type u) [CommRing K] (n t : ℕ) :
    Restricts ((cwSquarePartitionedTensor K dwz63Q).positivePower n).realize
      (dwz63PlainMarginalTypicalPower K n t).realize := by
  classical
  exact Tensor.Restricts.partitionedProjectionClosed
    ((cwSquarePartitionedTensor K dwz63Q).positivePower n)
    (dwz63PlainMarginalTypicalPower K n t).support Finset.univ
    (PartitionedTensor.select_support_isProjectionClosed_univ
      ((cwSquarePartitionedTensor K dwz63Q).positivePower n) (dwz63PlainMarginalKeep n t))

/-! ## The retained family at the plain marginal ambient -/

section Retained

variable {R : Type v} [Field R]

/-- **The family the plain hash retains at the marginal-typical ambient.**

The encoding is the committed `cwSquarePartitionHashEncoding`, whose only side condition is that
the five degree labels stay distinct in `R` --- satisfied in any characteristic at least five,
against the `15625` the six-orientation joint encoding needed. -/
noncomputable def dwz63PlainJointRetainedSupport (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
  (cwSquarePartitionHashEncoding hinj).markedXYIsolatedPowerAddresses n
    (dwz63PlainMarginalWords K n t) markedWords B seed

/-- **`hX` at the plain marginal ambient.** -/
theorem dwz63_x_injOn_plainJointRetained [NeZero (2 : R)] (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun address : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n) ↦ address .X)
      (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed : Set _) :=
  (cwSquarePartitionHashEncoding hinj).x_injectiveOn_markedXYIsolatedPowerAddresses n
    (dwz63PlainMarginalWords K n t) markedWords hmarked B hB seed

/-- **The good seed at the plain marginal-typical ambient.**

`[DuanWuZhou2022]`'s retention bound with the leg fibers measured against the marginal-typical
family.  The typical-count lane's fiber bound supplies `d = N_triple / N_X`, whose logarithm is
`H(α') - H(α_X) ≤ H(α) - H(α_X) + log K` per position. -/
theorem exists_seed_dwz63PlainJointRetained [Fintype R] [NeZero (2 : R)] (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R)) (d : ℕ)
    (hXfiber : ∀ triple ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        triple .X).card ≤ d)
    (hYfiber : ∀ triple ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card := by
  obtain ⟨seed, hcount, _hsubset, _hinjX, _hinjY⟩ :=
    (cwSquarePartitionHashEncoding hinj).exists_seed_many_markedXYIsolatedPowerAddresses_of_modulus
      n (dwz63PlainMarginalWords K n t) markedWords hmarked B hB d hXfiber hYfiber hmodulus
  exact ⟨seed, hcount⟩

end Retained

end AlgebraicComplexity.Examples
