/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetry
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareCounting
import AlgebraicComplexity.MatrixMultiplication.TypeExtraction

/-!
# Symmetry and restrictions for the ordinary CW-square constituents

The ordinary part of the squared Coppersmith--Winograd tensor consists of the three permutation
orbits represented by `004`, `013`, and `022`.  The representative restriction certificates are
proved in `CoppersmithWinogradSquare` and `CoppersmithWinogradSquareConstituents`; this file
transports them to every orientation.

The finite tensor work is explicit.  Each coarse constituent is expanded into its one, two, or
three raw source terms, and the generic address-level cycle/swap theorems transport those terms
through the degree-sum coarsening.  The final relation-level results combine these tensor
isomorphisms with the cyclic and transposition symmetries of matrix-multiplication tensors.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## Remaining ordinary addresses -/

abbrev cwSquare400 : CWSquareAddress := cwSquareCycleAddress cwSquare004
abbrev cwSquare040 : CWSquareAddress := cwSquareSwapAddress cwSquare004

abbrev cwSquare301 : CWSquareAddress := cwSquareCycleAddress cwSquare013
abbrev cwSquare130 : CWSquareAddress := cwSquareCycleAddress cwSquare301
abbrev cwSquare031 : CWSquareAddress := cwSquareSwapAddress cwSquare013
abbrev cwSquare103 : CWSquareAddress := cwSquareCycleAddress cwSquare031
abbrev cwSquare310 : CWSquareAddress := cwSquareSwapAddress cwSquare301

abbrev cwSquare202 : CWSquareAddress := cwSquareCycleAddress cwSquare022
abbrev cwSquare220 : CWSquareAddress := cwSquareSwapAddress cwSquare202

@[simp] theorem cwSquare400_eq : cwSquare400 = cwSquareAddress 4 0 0 := by decide
@[simp] theorem cwSquare040_eq : cwSquare040 = cwSquareAddress 0 4 0 := by decide
@[simp] theorem cwSquare301_eq : cwSquare301 = cwSquareAddress 3 0 1 := by decide
@[simp] theorem cwSquare130_eq : cwSquare130 = cwSquareAddress 1 3 0 := by decide
@[simp] theorem cwSquare031_eq : cwSquare031 = cwSquareAddress 0 3 1 := by decide
@[simp] theorem cwSquare103_eq : cwSquare103 = cwSquareAddress 1 0 3 := by decide
@[simp] theorem cwSquare310_eq : cwSquare310 = cwSquareAddress 3 1 0 := by decide
@[simp] theorem cwSquare202_eq : cwSquare202 = cwSquareAddress 2 0 2 := by decide
@[simp] theorem cwSquare220_eq : cwSquare220 = cwSquareAddress 2 2 0 := by decide

/-! ## Exact symmetry of the `004` orbit -/

/-- Cycling the `004` constituent produces the `400` constituent. -/
theorem cwSquareConstituent_004_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressCycleEquiv K q cwSquare004 c).toLinearMap)
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare004)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare400 := by
  rw [cwSquareConstituent_004, cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare400 =
      {cwSquareRawAddress cw200 cw200} by decide]
  simp only [Finset.sum_singleton]
  exact cwSquareCoarsenedTerm_cycleAt K q cwSquare004
    .zero .zero .last .zero .zero .last (by decide) (by decide) (by decide)

/-- Swapping `Y` and `Z` in `004` produces the third corner orientation `040`. -/
theorem cwSquareConstituent_004_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressSwapEquiv K q cwSquare004 c).toLinearMap)
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare004)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare040 := by
  rw [cwSquareConstituent_004, cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare040 =
      {cwSquareRawAddress cw020 cw020} by decide]
  simp only [Finset.sum_singleton]
  exact cwSquareCoarsenedTerm_swapAt K q cwSquare004
    .zero .zero .last .zero .zero .last (by decide) (by decide) (by decide)

/-! ## Exact symmetry of the `013` orbit -/

/-- Cycling `013` gives `301`, term by term in its two-element raw fiber. -/
theorem cwSquareConstituent_013_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressCycleEquiv K q cwSquare013 c).toLinearMap)
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare013)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare301 := by
  rw [cwSquareConstituent_013, cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare301 =
      {cwSquareRawAddress cw200 cw101,
        cwSquareRawAddress cw101 cw200} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareCoarsenedTerm_cycleAt K q cwSquare013
      .zero .zero .last .zero .middle .middle (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_cycleAt K q cwSquare013
      .zero .middle .middle .zero .zero .last (by decide) (by decide) (by decide)]

/-- A second cyclic step sends `301` to `130`. -/
theorem cwSquareConstituent_301_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressCycleEquiv K q cwSquare301 c).toLinearMap)
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare301)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare130 := by
  rw [cwSquareConstituent_eq_sum_sourceFiber,
    cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare301 =
      {cwSquareRawAddress cw200 cw101,
        cwSquareRawAddress cw101 cw200} by decide]
  rw [show cwSquareSourceFiber cwSquare130 =
      {cwSquareRawAddress cw020 cw110,
        cwSquareRawAddress cw110 cw020} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareCoarsenedTerm_cycleAt K q cwSquare301
      .last .zero .zero .middle .zero .middle (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_cycleAt K q cwSquare301
      .middle .zero .middle .last .zero .zero (by decide) (by decide) (by decide)]

/-- Swapping `Y` and `Z` sends `013` to `031`. -/
theorem cwSquareConstituent_013_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressSwapEquiv K q cwSquare013 c).toLinearMap)
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare013)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare031 := by
  rw [cwSquareConstituent_013, cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare031 =
      {cwSquareRawAddress cw020 cw011,
        cwSquareRawAddress cw011 cw020} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareCoarsenedTerm_swapAt K q cwSquare013
      .zero .zero .last .zero .middle .middle (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_swapAt K q cwSquare013
      .zero .middle .middle .zero .zero .last (by decide) (by decide) (by decide)]

/-- Cycling `031` gives `103`. -/
theorem cwSquareConstituent_031_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressCycleEquiv K q cwSquare031 c).toLinearMap)
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare031)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare103 := by
  rw [cwSquareConstituent_eq_sum_sourceFiber,
    cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare031 =
      {cwSquareRawAddress cw020 cw011,
        cwSquareRawAddress cw011 cw020} by decide]
  rw [show cwSquareSourceFiber cwSquare103 =
      {cwSquareRawAddress cw002 cw101,
        cwSquareRawAddress cw101 cw002} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareCoarsenedTerm_cycleAt K q cwSquare031
      .zero .last .zero .zero .middle .middle (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_cycleAt K q cwSquare031
      .zero .middle .middle .zero .last .zero (by decide) (by decide) (by decide)]

/-- Swapping `Y` and `Z` sends `301` to `310`. -/
theorem cwSquareConstituent_301_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressSwapEquiv K q cwSquare301 c).toLinearMap)
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare301)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare310 := by
  rw [cwSquareConstituent_eq_sum_sourceFiber,
    cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare301 =
      {cwSquareRawAddress cw200 cw101,
        cwSquareRawAddress cw101 cw200} by decide]
  rw [show cwSquareSourceFiber cwSquare310 =
      {cwSquareRawAddress cw200 cw110,
        cwSquareRawAddress cw110 cw200} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareCoarsenedTerm_swapAt K q cwSquare301
      .last .zero .zero .middle .zero .middle (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_swapAt K q cwSquare301
      .middle .zero .middle .last .zero .zero (by decide) (by decide) (by decide)]

/-! ## Exact symmetry of the `022` orbit -/

/-- Cycling `022` gives `202`, preserving its three raw branches. -/
theorem cwSquareConstituent_022_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressCycleEquiv K q cwSquare022 c).toLinearMap)
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare022)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare202 := by
  rw [cwSquareConstituent_022, cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare202 =
      {cwSquareRawAddress cw200 cw002,
        cwSquareRawAddress cw002 cw200,
        cwSquareRawAddress cw101 cw101} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareCoarsenedTerm_cycleAt K q cwSquare022
      .zero .zero .last .zero .last .zero (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_cycleAt K q cwSquare022
      .zero .last .zero .zero .zero .last (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_cycleAt K q cwSquare022
      .zero .middle .middle .zero .middle .middle (by decide) (by decide) (by decide)]
  abel

/-- Swapping `Y` and `Z` sends `202` to `220`. -/
theorem cwSquareConstituent_202_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    map (fun c ↦ (cwSquareAddressSwapEquiv K q cwSquare202 c).toLinearMap)
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare202)) =
      (cwSquarePartitionedTensor K q).constituent cwSquare220 := by
  rw [cwSquareConstituent_eq_sum_sourceFiber,
    cwSquareConstituent_eq_sum_sourceFiber]
  rw [show cwSquareSourceFiber cwSquare202 =
      {cwSquareRawAddress cw200 cw002,
        cwSquareRawAddress cw002 cw200,
        cwSquareRawAddress cw101 cw101} by decide]
  rw [show cwSquareSourceFiber cwSquare220 =
      {cwSquareRawAddress cw200 cw020,
        cwSquareRawAddress cw020 cw200,
        cwSquareRawAddress cw110 cw110} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [map_add]
  rw [cwSquareCoarsenedTerm_swapAt K q cwSquare202
      .last .zero .zero .zero .zero .last (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_swapAt K q cwSquare202
      .zero .zero .last .last .zero .zero (by decide) (by decide) (by decide),
    cwSquareCoarsenedTerm_swapAt K q cwSquare202
      .middle .zero .middle .middle .zero .middle (by decide) (by decide) (by decide)]

/-! ## Relation-level ordinary restrictions -/

/-- The exact `004 → 400` cyclic identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_004_isomorphic_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare004))
      ((cwSquarePartitionedTensor K q).constituent cwSquare400) := by
  refine ⟨cwSquareAddressCycleEquiv K q cwSquare004, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_004_cycle K q

/-- The exact `004 → 040` swap identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_004_isomorphic_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare004))
      ((cwSquarePartitionedTensor K q).constituent cwSquare040) := by
  refine ⟨cwSquareAddressSwapEquiv K q cwSquare004, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_004_swap K q

/-- The `400` ordinary corner constituent restricts to scalar multiplication. -/
theorem cwSquareConstituent_400_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare400)
      (matrixMultiplication (K := K) 1 1 1) := by
  exact (cwSquareConstituent_004_isomorphic_cycle K q).symm.restricts |>.trans
    (((cwSquareConstituent_004_restricts K q).permute cycle).trans
      (Tensor.Isomorphic.matrixMultiplication_cycle (K := K) 1 1 1).restricts)

/-- The `040` ordinary corner constituent restricts to scalar multiplication. -/
theorem cwSquareConstituent_040_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare040)
      (matrixMultiplication (K := K) 1 1 1) := by
  exact (cwSquareConstituent_004_isomorphic_swap K q).symm.restricts |>.trans
    (((cwSquareConstituent_004_restricts K q).permute xzy).trans
      (Tensor.Isomorphic.matrixMultiplication_swapYZ (K := K) 1 1 1).restricts)

/-- The exact `013 → 301` cyclic identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_013_isomorphic_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare013))
      ((cwSquarePartitionedTensor K q).constituent cwSquare301) := by
  refine ⟨cwSquareAddressCycleEquiv K q cwSquare013, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_013_cycle K q

/-- The exact `301 → 130` cyclic identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_301_isomorphic_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare301))
      ((cwSquarePartitionedTensor K q).constituent cwSquare130) := by
  refine ⟨cwSquareAddressCycleEquiv K q cwSquare301, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_301_cycle K q

/-- The exact `013 → 031` swap identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_013_isomorphic_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare013))
      ((cwSquarePartitionedTensor K q).constituent cwSquare031) := by
  refine ⟨cwSquareAddressSwapEquiv K q cwSquare013, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_013_swap K q

/-- The exact `031 → 103` cyclic identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_031_isomorphic_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare031))
      ((cwSquarePartitionedTensor K q).constituent cwSquare103) := by
  refine ⟨cwSquareAddressCycleEquiv K q cwSquare031, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_031_cycle K q

/-- The exact `301 → 310` swap identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_301_isomorphic_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare301))
      ((cwSquarePartitionedTensor K q).constituent cwSquare310) := by
  refine ⟨cwSquareAddressSwapEquiv K q cwSquare301, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_301_swap K q

/-- The `301` constituent restricts to `⟨2q,1,1⟩`. -/
theorem cwSquareConstituent_301_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare301)
      (matrixMultiplication (K := K) (2 * q) 1 1) := by
  exact (cwSquareConstituent_013_isomorphic_cycle K q).symm.restricts |>.trans
    (((cwSquareConstituent_013_restricts K q).permute cycle).trans
      (Tensor.Isomorphic.matrixMultiplication_cycle (K := K) 1 1 (2 * q)).restricts)

/-- The `130` constituent restricts to `⟨1,2q,1⟩`. -/
theorem cwSquareConstituent_130_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare130)
      (matrixMultiplication (K := K) 1 (2 * q) 1) := by
  exact (cwSquareConstituent_301_isomorphic_cycle K q).symm.restricts |>.trans
    (((cwSquareConstituent_301_restricts K q).permute cycle).trans
      (Tensor.Isomorphic.matrixMultiplication_cycle (K := K) (2 * q) 1 1).restricts)

/-- The `031` constituent restricts to `⟨1,1,2q⟩`. -/
theorem cwSquareConstituent_031_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare031)
      (matrixMultiplication (K := K) 1 1 (2 * q)) := by
  exact (cwSquareConstituent_013_isomorphic_swap K q).symm.restricts |>.trans
    (((cwSquareConstituent_013_restricts K q).permute xzy).trans
      (Tensor.Isomorphic.matrixMultiplication_swapYZ (K := K) 1 1 (2 * q)).restricts)

/-- The `103` constituent restricts to `⟨2q,1,1⟩`. -/
theorem cwSquareConstituent_103_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare103)
      (matrixMultiplication (K := K) (2 * q) 1 1) := by
  exact (cwSquareConstituent_031_isomorphic_cycle K q).symm.restricts |>.trans
    (((cwSquareConstituent_031_restricts K q).permute cycle).trans
      (Tensor.Isomorphic.matrixMultiplication_cycle (K := K) 1 1 (2 * q)).restricts)

/-- The `310` constituent restricts to `⟨1,2q,1⟩`. -/
theorem cwSquareConstituent_310_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare310)
      (matrixMultiplication (K := K) 1 (2 * q) 1) := by
  exact (cwSquareConstituent_301_isomorphic_swap K q).symm.restricts |>.trans
    (((cwSquareConstituent_301_restricts K q).permute xzy).trans
      (Tensor.Isomorphic.matrixMultiplication_swapYZ (K := K) (2 * q) 1 1).restricts)

/-- The exact `022 → 202` cyclic identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_022_isomorphic_cycle
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute cycle
        ((cwSquarePartitionedTensor K q).constituent cwSquare022))
      ((cwSquarePartitionedTensor K q).constituent cwSquare202) := by
  refine ⟨cwSquareAddressCycleEquiv K q cwSquare022, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_022_cycle K q

/-- The exact `202 → 220` swap identity, packaged as a tensor isomorphism. -/
theorem cwSquareConstituent_202_isomorphic_swap
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic
      (Tensor.permute xzy
        ((cwSquarePartitionedTensor K q).constituent cwSquare202))
      ((cwSquarePartitionedTensor K q).constituent cwSquare220) := by
  refine ⟨cwSquareAddressSwapEquiv K q cwSquare202, ?_⟩
  simpa [PiTensorProduct.congr] using cwSquareConstituent_202_swap K q

/-- The `202` constituent restricts to `⟨q²+2,1,1⟩`. -/
theorem cwSquareConstituent_202_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare202)
      (matrixMultiplication (K := K) (q ^ 2 + 2) 1 1) := by
  exact (cwSquareConstituent_022_isomorphic_cycle K q).symm.restricts |>.trans
    (((cwSquareConstituent_022_restricts K q).permute cycle).trans
      (Tensor.Isomorphic.matrixMultiplication_cycle (K := K) 1 1 (q ^ 2 + 2)).restricts)

/-- The `220` constituent restricts to `⟨1,q²+2,1⟩`. -/
theorem cwSquareConstituent_220_restricts
    (K : Type u) [CommRing K] (q : ℕ) :
    Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare220)
      (matrixMultiplication (K := K) 1 (q ^ 2 + 2) 1) := by
  exact (cwSquareConstituent_202_isomorphic_swap K q).symm.restricts |>.trans
    (((cwSquareConstituent_202_restricts K q).permute xzy).trans
      (Tensor.Isomorphic.matrixMultiplication_swapYZ (K := K) (q ^ 2 + 2) 1 1).restricts)

/-! ## A uniform finite restriction API for ordinary words -/

/-- First matrix dimension assigned to a square-support letter.  Exceptional letters receive
dimension zero so that the function extends to the full fifteen-letter support. -/
def cwSquareOrdinaryM (q : ℕ) (s : CWSquareAddress) : ℕ :=
  if s = cwSquareAddress 3 0 1 ∨ s = cwSquareAddress 1 0 3 then 2 * q
  else if s = cwSquareAddress 2 0 2 then q ^ 2 + 2
  else if s ∈ cwSquare112Orbit then 0
  else 1

/-- Second matrix dimension assigned to a square-support letter. -/
def cwSquareOrdinaryN (q : ℕ) (s : CWSquareAddress) : ℕ :=
  if s = cwSquareAddress 1 3 0 ∨ s = cwSquareAddress 3 1 0 then 2 * q
  else if s = cwSquareAddress 2 2 0 then q ^ 2 + 2
  else if s ∈ cwSquare112Orbit then 0
  else 1

/-- Third matrix dimension assigned to a square-support letter. -/
def cwSquareOrdinaryP (q : ℕ) (s : CWSquareAddress) : ℕ :=
  if s = cwSquareAddress 0 1 3 ∨ s = cwSquareAddress 0 3 1 then 2 * q
  else if s = cwSquareAddress 0 2 2 then q ^ 2 + 2
  else if s ∈ cwSquare112Orbit then 0
  else 1

/-- Every square constituent has the uniform ordinary-or-zero restriction specified by
`cwSquareOrdinaryM/N/P`.

For the twelve ordinary letters this is the exact oriented matrix-multiplication restriction.
For `112`, `121`, and `211`, all dimensions are zero and the statement is the canonical zero
restriction.  This total formulation allows the generic typed-word theorem to be applied before
using the fact that an ordinary profile assigns multiplicity zero to exceptional letters.

Proof sketch: enumerate the fifteen proved support addresses.  Apply the representative or
transported ordinary restriction in twelve cases, and the zero-leg map in the remaining three. -/
theorem cwSquareConstituent_restricts_ordinaryOrZero
    (K : Type u) [CommRing K] (q : ℕ) (s : CWSquareSupport) :
    Restricts ((cwSquarePartitionedTensor K q).constituent s.1)
      (matrixMultiplication (K := K)
        (cwSquareOrdinaryM q s.1) (cwSquareOrdinaryN q s.1)
        (cwSquareOrdinaryP q s.1)) := by
  rcases s with ⟨s, hs⟩
  rw [cwSquareSupport_eq_antidiagonal] at hs
  simp only [cwSquareAntidiagonal, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    change Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare004)
      (matrixMultiplication (K := K) 1 1 1)
    exact cwSquareConstituent_004_restricts K q
  · simp only [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    change Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare013)
      (matrixMultiplication (K := K) 1 1 (2 * q))
    exact cwSquareConstituent_013_restricts K q
  · simp only [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    change Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare022)
      (matrixMultiplication (K := K) 1 1 (q ^ 2 + 2))
    exact cwSquareConstituent_022_restricts K q
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_031_restricts K q
    rw [cwSquare031_eq] at h
    exact h
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_040_restricts K q
    rw [cwSquare040_eq] at h
    exact h
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_103_restricts K q
    rw [cwSquare103_eq] at h
    exact h
  · simp only [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    change Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare112)
      (matrixMultiplication (K := K) 0 0 0)
    rw [show matrixMultiplication (K := K) 0 0 0 = 0 by
      simp [matrixMultiplication]]
    exact Tensor.Restricts.zeroTarget _
  · simp only [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    change Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare121)
      (matrixMultiplication (K := K) 0 0 0)
    rw [show matrixMultiplication (K := K) 0 0 0 = 0 by
      simp [matrixMultiplication]]
    exact Tensor.Restricts.zeroTarget _
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_130_restricts K q
    rw [cwSquare130_eq] at h
    exact h
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_202_restricts K q
    rw [cwSquare202_eq] at h
    exact h
  · simp only [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    change Restricts ((cwSquarePartitionedTensor K q).constituent cwSquare211)
      (matrixMultiplication (K := K) 0 0 0)
    rw [show matrixMultiplication (K := K) 0 0 0 = 0 by
      simp [matrixMultiplication]]
    exact Tensor.Restricts.zeroTarget _
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_220_restricts K q
    rw [cwSquare220_eq] at h
    exact h
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_301_restricts K q
    rw [cwSquare301_eq] at h
    exact h
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_310_restricts K q
    rw [cwSquare310_eq] at h
    exact h
  · simp [cwSquareOrdinaryM, cwSquareOrdinaryN, cwSquareOrdinaryP,
      cwSquare112Orbit, cwSquareAddress_eq_iff, reduceIte]
    have h := cwSquareConstituent_400_restricts K q
    rw [cwSquare400_eq] at h
    exact h

end AlgebraicComplexity.Examples
