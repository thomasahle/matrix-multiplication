/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalLeafAssembly
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAggregateBatching
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchLoss
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMargin

set_option autoImplicit false

/-!
# The joined split distribution and the reference leaf's weight

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`'s §6.3 fixes the level-two
parameters (`papers/sources/2210.10173/global_value.tex:332-378`, `table:result-2nd`); this module
carries the two pieces of that instantiation which are independent of the hole family:

* `dwz63JoinedAlphaTilde s` --- the fifteen-component split distribution at the joined period,
  `t ↦ proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)`.  It is the inline lambda that
  `Examples/DuanWuZhouLevelTwoRegionalLeafAssembly.lean` and
  `Examples/DuanWuZhouLevelTwoRegionalCells.lean` both use, given a name so that the stage and the
  leaf weight can be seen to talk about the same `alphaTilde`.
* `dwz63_referenceLeafAssembly_leafWeight` --- the whole reference leaf's `HasTauWeight` at the
  margin-shifted value, from `dwz63_hasTauWeight_symSix_referenceLeaf`, reindexed so that the
  period, the reference word and the orbit premise are functions of the endpoint's index `j`.

## What used to be here

The stage half and the combined telescope have been removed.  They were built on
`dwz63_plainPreimageSymSixStage` and the pre-cut hole family, which the Step-One cut
supersedes: the endpoint now runs through `dwz63_cutReferenceLeafAssembly_stage_marked`
(`Examples/DuanWuZhouLevelTwoStepOneCutAssemblyMarked.lean`) at `dwz63CutReferenceHoles`
(`Examples/DuanWuZhouLevelTwoStepOneCutHoles.lean`).  Nothing consumed the removed theorems: the
live chain reaches the endpoint through `…AssemblyMarked` and `…AssemblyMarkedSeededLoss`.

Keeping this module free of the superseded hole family is what lets
`Examples/DuanWuZhouLevelTwoStepOneCutAssemblyMarked.lean` import it --- it uses
`dwz63JoinedAlphaTilde` --- without pulling the degenerate family back into the endpoint's cone.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

noncomputable section

/-! ## The per-segment type at the joined period -/

/-- **The fifteen-component split distribution at the joined period `s`.**  This is the inline
lambda that `Examples/DuanWuZhouLevelTwoRegionalLeafAssembly.lean:179` and
`Examples/DuanWuZhouLevelTwoRegionalCells.lean:198` both use, given a name so that the stage and
the leaf weight can be seen to be talking about the same `alphaTilde`. -/
def dwz63JoinedAlphaTilde (s : ℕ) : Fin 15 → PositiveWord CWBlock 1 → ℕ :=
  fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)

@[simp] theorem dwz63JoinedAlphaTilde_apply (s : ℕ) (t : Fin 15) :
    dwz63JoinedAlphaTilde s t
      = WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s) := rfl

/-! ## The leaf-weight half -/

section LeafWeight

variable (K : Type u) [CommRing K]

/-- **The whole reference leaf carries the margin-shifted value, at every joined period.**

`dwz63_hasTauWeight_symSix_referenceLeaf` reindexed so that the period, the reference word and the
orbit premise are all functions of the endpoint's index `j`.  The two carried premises are the
residuals `R2` (the reference word's fifteen-segment profile) and `R3` (`hcut`, the three orbit
rows of image 109, whose cofinality the client supplies). -/
theorem dwz63_referenceLeafAssembly_leafWeight (margin : ℝ) (hmargin : 0 < margin) :
    ∃ N : ℕ, ∀ (len s : ℕ → ℕ),
      (∀ j : ℕ, N ≤ s j) →
      ∀ wRef : ∀ j : ℕ, PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) (len j),
        (∀ (j : ℕ) (t : Fin 15),
          WordType.multiplicity (dwz63Seg K (len j) (wRef j)) t
            = 200000000 * (dwz63Alpha t * s j)) →
        (∀ (j : ℕ) (o : Fin 3) (m : ℕ),
          m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s j) →
          HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
            (dwz63Alpha (dwz63OrbitRow o) * s j)).realize) dwz63Tau
            (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s j : ℕ) : ℝ)
              * (dwz63OrbitLogVal o - margin)) ^ 3)) →
        ∀ j : ℕ,
          HasTauWeight K
            (symSix K
              (dwz63ReferenceLeaf K (len j) (dwz63JoinedAlphaTilde (s j)) (wRef j)).realize)
            dwz63Tau (Real.exp (((len j : ℝ) + 1) * (dwz63LogVal - margin)) ^ 6) := by
  obtain ⟨N, hN⟩ := dwz63_hasTauWeight_symSix_referenceLeaf K margin hmargin
  exact ⟨N, fun len s hs wRef hmu hcut j ↦
    hN (s j) (hs j) (hcut j) (len j) (wRef j) (hmu j)⟩

end LeafWeight


end

end AlgebraicComplexity.Examples
