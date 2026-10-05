/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroInterface
import AlgebraicComplexity.MatrixMultiplication.CTensorFiberEnumeration

/-!
# Retyping an exact zero-coordinate CW interface as a C-tensor

The zero-coordinate support theorem gives one shared block on `Z` and injective block labels on
`X` and `Y`.  This module feeds those facts to the generic finite-fiber enumerator.  The result is
an explicit restriction of the whole selected interface tensor to a C-tensor with exactly the
same number of constituents as the selected support.

At this stage each constituent is embedded in the common ambient partitioned leg spaces.  The
subsequent one-slice specialization must prove that these constituents share the certificate's
uniform local `q`-power; that numerical-semantic identification is intentionally not assumed here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- Block spaces of the outer positive power used by one exact CW interface term. -/
abbrev CWExactInterfaceBlockSpace
    (K : Type u) [CommRing K] (q depth n : ℕ) :=
  PositivePowerBlockSpace K
    (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) (2 ^ depth - 1)) n

/-- Canonical whole-support C-tensor retyping of a zero-`Z` exact CW interface term.

The target leg spaces are the full ambient partitioned spaces.  Consequently the only linear
maps used here are block inclusions, and no local constituent restriction is hidden in the
constructor. -/
noncomputable def cwSelectedExactInterfaceTerm_zeroZ_ambientFiberRetyping
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    CTensor.FiberRetyping
      (X := PartitionedSpace K (CWExactInterfaceBlockSpace K q depth n) .X)
      (Y := PartitionedSpace K (CWExactInterfaceBlockSpace K q depth n) .Y)
      (Z := PartitionedSpace K (CWExactInterfaceBlockSpace K q depth n) .Z)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card := by
  let P := cwSelectedExactInterfaceTerm K q term hmultiplicity
  have hsupport := cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber
    K q term hmultiplicity hz
  exact CTensor.FiberRetyping.ofSharedSupportAmbient
    P P.support hsupport.2.1 hsupport.2.2
      (cwZeroInterfaceLegWord depth n) hsupport.1

/-- The entire exact zero-`Z` interface tensor restricts to its canonically enumerated C-tensor.

In particular, the C-tensor has `support.card` constituents.  This theorem performs no
representative selection. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_restricts_ambientCTensor
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    Restricts
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (CTensor.partitioned
        (cwSelectedExactInterfaceTerm_zeroZ_ambientFiberRetyping
          K q term hmultiplicity hz).targetConstituent).realize := by
  let C := cwSelectedExactInterfaceTerm_zeroZ_ambientFiberRetyping
    K q term hmultiplicity hz
  simpa [C, PartitionedTensor.withSupport] using C.restricts_partitioned

end AlgebraicComplexity.Examples
