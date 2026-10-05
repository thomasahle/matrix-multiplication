import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightNestedComposition
import MatrixMultiplication.TotalWeightVolumeEndpoint

set_option autoImplicit false

/-!
# Concrete nested-sequence endpoint for the total-weight certificate

This module is the final paper-independent assembly boundary for the requested Lean theorem.
The outer certificate supplies whole localized total-weight constituents; the canonical inner
certificate extracts an equal rectangular matrix-multiplication family from each constituent.
Their retained exponents add, while the rectangular-volume exponent is counted exactly once.

No numerical or tensor-extraction premise is hidden here.  The two structures consumed by the
theorem are the semantic sequences constructed by the finite hashing and typed-leaf modules.
-/

namespace MatrixMultiplication.TotalWeightLeanEndpoint

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightVolumeEndpoint

universe u w x

/-- A concrete total-weight outer sequence and its canonical copywise inner extraction imply the
requested endpoint as soon as their three semantic rates clear the deliberately coarse rational
floors.  This theorem is the final adapter used by the certificate-specific constructor. -/
theorem omega_lt_236999_of_nestedSequenceData
    (K : Type u) [Field K]
    {stride : ℕ} {outerRetained innerRetained volume : ℝ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, w}
      K 5 4 (Tensor.power (coppersmithWinograd K 5) 8) stride
        ((2 : ℝ) ^ ((stride : ℝ) * outerRetained)))
    (inner : CWTotalWeightLocalizedOuterSequenceData.CanonicalInnerSequenceData.{u, u, w, x}
      outer ((2 : ℝ) ^ ((stride : ℝ) * innerRetained))
        ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (houter : acceptanceOuterRetainedFloor ≤ outerRetained)
    (hinner : acceptanceInnerRetainedFloor ≤ innerRetained)
    (hvolume : volumeFloor ≤ volume) :
    omega K < acceptanceTarget := by
  exact omega_lt_236999_of_subexponentialVolumeSequence_outer_inner_floors K
    inner.toSubexponentialLaserVolumeSequence_addRetained
    houter hinner hvolume

/-- Specialization in which the semantic sequence constructors are parameterized directly by
the three acceptance floors.  The final certificate theorem therefore only has to construct the
two sequence records; all real-exponent arithmetic is definitionally fixed here. -/
theorem omega_lt_236999_of_nestedAcceptanceData
    (K : Type u) [Field K]
    {stride : ℕ}
    (outer : CWTotalWeightLocalizedOuterSequenceData.{u, u, w}
      K 5 4 (Tensor.power (coppersmithWinograd K 5) 8) stride
        ((2 : ℝ) ^ ((stride : ℝ) * acceptanceOuterRetainedFloor)))
    (inner : CWTotalWeightLocalizedOuterSequenceData.CanonicalInnerSequenceData.{u, u, w, x}
      outer ((2 : ℝ) ^ ((stride : ℝ) * acceptanceInnerRetainedFloor))
        ((2 : ℝ) ^ (3 * (stride : ℝ) * volumeFloor))) :
    omega K < acceptanceTarget := by
  exact omega_lt_236999_of_nestedSequenceData K outer inner le_rfl le_rfl le_rfl

end MatrixMultiplication.TotalWeightLeanEndpoint
