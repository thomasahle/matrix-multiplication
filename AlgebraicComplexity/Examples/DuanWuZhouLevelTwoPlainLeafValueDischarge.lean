/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainLeafValue

set_option autoImplicit false

/-!
# Discharging the two values-idiom hypotheses of the plain leaf

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/DuanWuZhouLevelTwoPlainLeafValue.lean` leaves `dwz63_hasTauWeight_symSix_plainLeaf_logVal`
with two hypotheses stated in the values lane's own idiom, exactly as
`dwz63_hasTauWeight_component` leaves the three orbit weights.  This module discharges both.

* `hcell` --- the twelve non-orbit per-cell weights.  `dwz63CellEquiv` names the cell, and the
  twelve committed weights `dwz63_hasTauWeight_004 … _202` supply it.  There is nothing to choose:
  the fifteen cells minus the three of the `(1,1,2)` orbit are exactly the twelve addresses those
  lemmas cover.
* `hwa`, `hwb`, `hwc` --- the three orbit certificates at the leaf's own exponents.  The certificate
  comes in blocks of `dwz121Mass`, so the scale is taken along `t = dwz121Mass * j`; then
  `alpha_s * t = dwz121Mass * (alpha_s * j)` is a whole number of blocks and `alpha_s * j ≥ j`
  clears the certificate's cutoff.  This is stage-index arithmetic only.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The twelve non-orbit cell weights -/

section Cells

variable (K : Type u) [CommRing K]

set_option maxRecDepth 20000 in
/-- **The twelve non-orbit coarse addresses, enumerated.**  Stated against the degree-four
antidiagonal condition rather than `Finset` membership in the image, so the decision procedure
does not have to recompute `cwSquareSupport`. -/
theorem dwz63_nonOrbit_cases (a : CWSquareAddress)
    (ha : (a .X).val + (a .Y).val + (a .Z).val = 4) (hna : a ∉ cwSquare112Orbit) :
    a = cwSquare004 ∨ a = cwSquare013 ∨ a = cwSquare022 ∨ a = cwSquare031 ∨ a = cwSquare040 ∨
      a = cwSquare103 ∨ a = cwSquare130 ∨ a = cwSquare202 ∨ a = cwSquare220 ∨
      a = cwSquare301 ∨ a = cwSquare310 ∨ a = cwSquare400 := by
  revert a
  decide

set_option maxHeartbeats 1000000 in
/-- **Every non-orbit coarse cell carries its section 6.3 value.**

This is `hcell` of `dwz63_hasTauWeight_symSix_plainLeaf_logVal`.  The twelve committed weights
`dwz63_hasTauWeight_004 … _202` are exactly the fifteen cells minus the three of the `(1,1,2)`
orbit; there is nothing to choose. -/
theorem dwz63_hasTauWeight_nonOrbitCell
    (s : (cwSquarePartitionedTensor K dwz63Q).support) (hs : s.1 ∉ cwSquare112Orbit) :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s.1) dwz63Tau
      (dwz63ValOf s.1) := by
  have hmem : s.1 ∈ cwSquareAntidiagonal := by
    rw [← cwSquareSupport_eq_antidiagonal]
    exact s.2
  have hdeg : ((s.1) .X).val + ((s.1) .Y).val + ((s.1) .Z).val = 4 :=
    (mem_cwSquareAntidiagonal_iff _).mp hmem
  rcases dwz63_nonOrbit_cases s.1 hdeg hs with
    h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
  · exact (dwz63_hasTauWeight_004 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_013 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_022 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_031 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_040 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_103 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_130 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_202 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_220 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_301 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_310 K).mono (le_of_eq rfl)
  · exact (dwz63_hasTauWeight_400 K).mono (le_of_eq rfl)

end Cells

/-! ## The three orbit certificates at the leaf's exponents -/

section Certificates

variable (K : Type u) [Field K]

/-- `dwz63Alpha112` is positive. -/
theorem dwz63Alpha112_pos : 0 < dwz63Alpha112 := by norm_num [dwz63Alpha112]

/-- `dwz63Alpha121` is positive. -/
theorem dwz63Alpha121_pos : 0 < dwz63Alpha121 := by norm_num [dwz63Alpha121]

/-- **The orbit certificate at a cell, at every exponent of the form `alpha * (dwz121Mass * j)`.**

The certificate is delivered in blocks of `dwz121Mass`; taking the scale along
`t = dwz121Mass * j` makes `alpha * t` a whole number of blocks, and `alpha * j ≥ j` clears the
certificate's own cutoff. -/
theorem dwz63_hasTauWeight_power_symSix_orbitCell_scaled
    (s : CWSquareAddress) (hs : s ∈ cwSquare112Orbit) (a : ℕ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      HasTauWeight K
        (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent s))
          (a * (dwz121Mass * j)))
        dwz63Tau ((dwz121LeafTerm K ^ (3 * (a * (dwz121Mass * j)))) ^ 2) := by
  obtain ⟨N, hN⟩ := dwz63_hasTauWeight_power_symSix_orbitCell K s hs
  refine ⟨N, fun j hj ↦ ?_⟩
  have hblocks : a * (dwz121Mass * j) = dwz121Mass * (a * j) := by ring
  have hcut : N ≤ a * j := le_trans hj (Nat.le_mul_of_pos_left j ha)
  rw [hblocks]
  exact hN (a * j) hcut

/-- **All three orbit certificates hold cofinally, at one common scale.**

This is `hwa`, `hwb`, `hwc` of `dwz63_hasTauWeight_symSix_plainLeaf_logVal`, at the scale
`t = dwz121Mass * j`: the exponents are then `dwz63Alpha112 * t` and `dwz63Alpha121 * t`, which is
exactly what the leaf's typical multiplicities ask for. -/
theorem dwz63_exists_orbitCertificates :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      HasTauWeight K
        (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112))
          (dwz63Alpha112 * (dwz121Mass * j))) dwz63Tau
        ((dwz121LeafTerm K ^ (3 * (dwz63Alpha112 * (dwz121Mass * j)))) ^ 2)
      ∧ HasTauWeight K
        (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121))
          (dwz63Alpha121 * (dwz121Mass * j))) dwz63Tau
        ((dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * (dwz121Mass * j)))) ^ 2)
      ∧ HasTauWeight K
        (Tensor.power (symSix K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211))
          (dwz63Alpha121 * (dwz121Mass * j))) dwz63Tau
        ((dwz121LeafTerm K ^ (3 * (dwz63Alpha121 * (dwz121Mass * j)))) ^ 2) := by
  obtain ⟨Na, hNa⟩ := dwz63_hasTauWeight_power_symSix_orbitCell_scaled K cwSquare112
    (by decide) dwz63Alpha112 dwz63Alpha112_pos
  obtain ⟨Nb, hNb⟩ := dwz63_hasTauWeight_power_symSix_orbitCell_scaled K cwSquare121
    (by decide) dwz63Alpha121 dwz63Alpha121_pos
  obtain ⟨Nc, hNc⟩ := dwz63_hasTauWeight_power_symSix_orbitCell_scaled K cwSquare211
    (by decide) dwz63Alpha121 dwz63Alpha121_pos
  refine ⟨max Na (max Nb Nc), fun j hj ↦ ⟨?_, ?_, ?_⟩⟩
  · exact hNa j (le_trans (le_max_left _ _) hj)
  · exact hNb j (le_trans (le_trans (le_max_left Nb Nc) (le_max_right Na _)) hj)
  · exact hNc j (le_trans (le_trans (le_max_right Nb Nc) (le_max_right Na _)) hj)

end Certificates

end AlgebraicComplexity.Examples
