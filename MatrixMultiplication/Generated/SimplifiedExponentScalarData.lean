import MatrixMultiplication.Generated.SimplifiedExponentScalarPositiveData0
import MatrixMultiplication.Generated.SimplifiedExponentScalarNegativeData0

/-!
# Generated retained-exponent lower witness

Generated from certificate SHA-256 `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`.  Positive logarithms were compressed by
concavity chords and negative logarithms by tangents at exact coefficient-weighted means.  The
result is a conservative lower witness; the semantic recurrence adapter is responsible for
showing that this witness is at most the retained base-two copy exponent.
-/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentScalar

open MatrixMultiplication.DyadicEntropy

noncomputable section

def bits : ℕ := 112
def constantNumerator : ℕ := 219875289900727070445243759082703113
def inverseLogCoefficient : ℝ := -151277108086821679585903427454212147525557101871072428977154948875927432297261139713820609699680630512136070543042582245939086248485413685797231787 / 155816307925261998621044749748317782053322090567626567279263547944504053974105117649352936864723590086559678872183001771658313130859483034851423027200

def positiveExactSum : ℝ :=
  Positive0.exact

def positiveFloorSum : ℝ :=
  Positive0.floor

def negativeExactSum : ℝ :=
  Negative0.exact

def negativeCeilingSum : ℝ :=
  Negative0.ceiling

def inverseLogTerm : ℝ := inverseLogCoefficient / Real.log 2
def inverseLogFloor : ℝ := -350166707 / 250000000000

theorem inverseLogFloor_le : inverseLogFloor ≤ inverseLogTerm := by
  unfold inverseLogTerm
  apply le_trans (b :=
      inverseLogCoefficient / MatrixMultiplication.FastDyadicLog.fastLogTwoLower)
  · norm_num [inverseLogFloor, inverseLogCoefficient,
      MatrixMultiplication.FastDyadicLog.fastLogTwoLower]
  · have hlower : MatrixMultiplication.FastDyadicLog.fastLogTwoLower ≤ Real.log 2 :=
      MatrixMultiplication.FastDyadicLog.fastLogTwoLower_le_logTwoLower.trans
        MatrixMultiplication.LogBounds.logTwoLower_le_logTwo
    have hpositive := div_le_div_of_nonneg_left
      (show 0 ≤ -inverseLogCoefficient by norm_num [inverseLogCoefficient])
      (by norm_num [MatrixMultiplication.FastDyadicLog.fastLogTwoLower]) hlower
    simpa only [neg_div, neg_neg] using neg_le_neg hpositive

/-- Exact real value of the compressed, conservative retained-exponent witness. -/
def retainedExponentLowerWitness : ℝ :=
  mass bits constantNumerator + positiveExactSum - negativeExactSum + inverseLogTerm

/-- Fully rational endpoint assembled from independently sealed logarithm chunks. -/
def retainedExponentRationalFloor : ℝ :=
  mass bits constantNumerator + positiveFloorSum - negativeCeilingSum + inverseLogFloor

theorem retainedExponentRationalFloor_le :
    retainedExponentRationalFloor ≤ retainedExponentLowerWitness := by
  have hpositive0 := Positive0.exact_bound
  have hnegative0 := Negative0.exact_bound
  have hinverse := inverseLogFloor_le
  unfold retainedExponentRationalFloor retainedExponentLowerWitness
    positiveFloorSum positiveExactSum negativeCeilingSum negativeExactSum
  linarith

/-- The compressed exact witness is already strictly larger than `8.2`. -/
theorem eightPointTwo_lt_retainedExponentLowerWitness :
    (82 / 10 : ℝ) < retainedExponentLowerWitness := by
  apply lt_of_lt_of_le (b := retainedExponentRationalFloor) ?_
    retainedExponentRationalFloor_le
  norm_num [retainedExponentRationalFloor, positiveFloorSum, negativeCeilingSum,
    bits, constantNumerator, inverseLogFloor, Positive0.floor, Negative0.ceiling, mass]

/-- Narrow numerical interface: any semantic retained exponent above the exact witness exceeds
`8.2`. -/
theorem eightPointTwo_lt_of_witness_le {retainedExponent : ℝ}
    (hwitness : retainedExponentLowerWitness ≤ retainedExponent) :
    (82 / 10 : ℝ) < retainedExponent :=
  eightPointTwo_lt_retainedExponentLowerWitness.trans_le hwitness

end

end MatrixMultiplication.Generated.SimplifiedExponentScalar
