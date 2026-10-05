/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.FastDyadicLog

/-!
# Executable rational form of the fast dyadic logarithm bounds

`FastDyadicLog` states its certified endpoints in `ℝ`, because they are ultimately compared with
the real logarithm.  Every endpoint calculation itself is rational, however.  This file mirrors
that calculation in `ℚ` and proves once that casting the result to `ℝ` recovers the analytic
definition.

Generated certificates can consequently check thousands of closed endpoint comparisons with the
kernel's decidable rational order, then transport only the final result to `ℝ`.  This avoids
asking `norm_num` to rediscover the same rational normalization separately at every occurrence.
-/

open scoped BigOperators

namespace MatrixMultiplication.RationalDyadicLog

open AlgebraicComplexity.Analysis

/-- Rational reduction of an integer numerator to the atanh interval. -/
def reducedArgument (numerator scale : ℕ) : ℚ :=
  ((numerator : ℚ) - (2 : ℚ) ^ scale) /
    ((numerator : ℚ) + (2 : ℚ) ^ scale)

/-- Rational atanh partial sum used by the lower endpoint. -/
def atanhPartial (x : ℚ) (steps : ℕ) : ℚ :=
  ∑ k ∈ Finset.range steps, x ^ (2 * k + 1) / (2 * k + 1)

/-- Rational geometric remainder used by the upper endpoint. -/
def atanhRemainder (x : ℚ) (steps : ℕ) : ℚ :=
  x ^ (2 * steps + 1) / (1 - x ^ 2)

/-- Rational lower enclosure for the full logarithm ratio. -/
def logRatioLower (x : ℚ) (steps : ℕ) : ℚ :=
  2 * atanhPartial x steps

/-- Rational upper enclosure for the full logarithm ratio. -/
def logRatioUpper (x : ℚ) (steps : ℕ) : ℚ :=
  2 * (atanhPartial x steps + atanhRemainder x steps)

/-- Exact rational represented by `FastDyadicLog.fastLogTwoLower`. -/
def fastLogTwoLower : ℚ := 693147180559945 / 1000000000000000

/-- Exact rational represented by `FastDyadicLog.fastLogTwoUpper`. -/
def fastLogTwoUpper : ℚ := 693147180559946 / 1000000000000000

/-- Executable rational lower endpoint for `log₂ numerator`. -/
def numeratorLogLower (numerator scale steps : ℕ) : ℚ :=
  scale + logRatioLower (reducedArgument numerator scale) steps / fastLogTwoUpper

/-- Executable rational upper endpoint for `log₂ numerator`. -/
def numeratorLogUpper (numerator scale steps : ℕ) : ℚ :=
  scale + logRatioUpper (reducedArgument numerator scale) steps / fastLogTwoLower

/-- Casting the rational reduced argument to `ℝ` gives the analytic reduced argument. -/
@[simp] theorem cast_reducedArgument (numerator scale : ℕ) :
    (reducedArgument numerator scale : ℝ) =
      MatrixMultiplication.DyadicEntropy.reducedArgument numerator scale := by
  simp [reducedArgument, MatrixMultiplication.DyadicEntropy.reducedArgument]

/-- Casting a rational atanh partial sum commutes with its finite sum. -/
@[simp] theorem cast_atanhPartial (x : ℚ) (steps : ℕ) :
    (atanhPartial x steps : ℝ) =
      AlgebraicComplexity.Analysis.atanhPartial (x : ℝ) steps := by
  simp [atanhPartial, AlgebraicComplexity.Analysis.atanhPartial]

/-- Casting the rational remainder gives the analytic remainder. -/
@[simp] theorem cast_atanhRemainder (x : ℚ) (steps : ℕ) :
    (atanhRemainder x steps : ℝ) =
      AlgebraicComplexity.Analysis.atanhRemainder (x : ℝ) steps := by
  simp [atanhRemainder, AlgebraicComplexity.Analysis.atanhRemainder]

/-- Casting the rational lower ratio endpoint gives the analytic endpoint. -/
@[simp] theorem cast_logRatioLower (x : ℚ) (steps : ℕ) :
    (logRatioLower x steps : ℝ) =
      AlgebraicComplexity.Analysis.logRatioLower (x : ℝ) steps := by
  simp [logRatioLower, AlgebraicComplexity.Analysis.logRatioLower]

/-- Casting the rational upper ratio endpoint gives the analytic endpoint. -/
@[simp] theorem cast_logRatioUpper (x : ℚ) (steps : ℕ) :
    (logRatioUpper x steps : ℝ) =
      AlgebraicComplexity.Analysis.logRatioUpper (x : ℝ) steps := by
  simp [logRatioUpper, AlgebraicComplexity.Analysis.logRatioUpper]

/-- The rational lower `log 2` endpoint casts to the existing real definition. -/
@[simp] theorem cast_fastLogTwoLower :
    (fastLogTwoLower : ℝ) = MatrixMultiplication.FastDyadicLog.fastLogTwoLower := by
  norm_num [fastLogTwoLower, MatrixMultiplication.FastDyadicLog.fastLogTwoLower]

/-- The rational upper `log 2` endpoint casts to the existing real definition. -/
@[simp] theorem cast_fastLogTwoUpper :
    (fastLogTwoUpper : ℝ) = MatrixMultiplication.FastDyadicLog.fastLogTwoUpper := by
  norm_num [fastLogTwoUpper, MatrixMultiplication.FastDyadicLog.fastLogTwoUpper]

/-- The executable rational lower endpoint casts to `FastDyadicLog.numeratorLogLower`. -/
@[simp] theorem cast_numeratorLogLower (numerator scale steps : ℕ) :
    (numeratorLogLower numerator scale steps : ℝ) =
      MatrixMultiplication.FastDyadicLog.numeratorLogLower numerator scale steps := by
  simp [numeratorLogLower, MatrixMultiplication.FastDyadicLog.numeratorLogLower]

/-- The executable rational upper endpoint casts to `FastDyadicLog.numeratorLogUpper`. -/
@[simp] theorem cast_numeratorLogUpper (numerator scale steps : ℕ) :
    (numeratorLogUpper numerator scale steps : ℝ) =
      MatrixMultiplication.FastDyadicLog.numeratorLogUpper numerator scale steps := by
  simp [numeratorLogUpper, MatrixMultiplication.FastDyadicLog.numeratorLogUpper]

/-- A decidable rational lower comparison transports to the certified real endpoint. -/
theorem cast_le_fastLower {bound : ℚ} {numerator scale steps : ℕ}
    (hbound : bound ≤ numeratorLogLower numerator scale steps) :
    (bound : ℝ) ≤
      MatrixMultiplication.FastDyadicLog.numeratorLogLower numerator scale steps := by
  rw [← cast_numeratorLogLower]
  exact Rat.cast_le.mpr hbound

/-- A decidable rational upper comparison transports to the certified real endpoint. -/
theorem fastUpper_le_cast {bound : ℚ} {numerator scale steps : ℕ}
    (hbound : numeratorLogUpper numerator scale steps ≤ bound) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper numerator scale steps ≤
      (bound : ℝ) := by
  rw [← cast_numeratorLogUpper]
  exact Rat.cast_le.mpr hbound

end MatrixMultiplication.RationalDyadicLog
