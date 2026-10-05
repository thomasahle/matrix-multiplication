/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropyList

/-!
# Finite compatibility-row data

This module contains the certificate-free row representation shared by recursive entropy
evaluators and semantic compatibility-counting theorems.  It deliberately has no dependency on
a particular recursion depth, tensor construction, or numerical certificate.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedExponentRootRecurrence

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm

noncomputable section

variable {A X : Type*}

/-- Serialize a finite numerator family in canonical `Fintype` order. -/
def numeratorList [Fintype A] [DecidableEq A] (numerator : A → ℕ) : List ℕ :=
  Finset.univ.toList.map numerator

/-- Exact numerator of a pushed-forward coordinate marginal. -/
def marginalNumerator [Fintype A] [DecidableEq X]
    (coord : A → X) (numerator : A → ℕ) (x : X) : ℕ :=
  ∑ state, if coord state = x then numerator state else 0

/-- A compatibility branch is one pooled parent row minus two finite collections of entropy
rows: individually charged boundary rows and pooled compatibility-cell rows. -/
structure CompatibilityRows where
  pooled : List ℕ
  first : List (List ℕ)
  groups : List (List ℕ)
  deriving DecidableEq, Repr

namespace CompatibilityRows

/-- Real homogeneous-entropy value of one compatibility branch. -/
def rate (bits : ℕ) (rows : CompatibilityRows) : ℝ :=
  weightedEntropyList bits rows.pooled -
    (rows.first.map (weightedEntropyList bits)).sum -
    (rows.groups.map (weightedEntropyList bits)).sum

/-- Compatibility rates agree whenever the three entropy components agree.  This is the intended
interface for compact certificates: their serialized rows may differ from canonical semantic
rows by support order and zero padding, so clients prove entropy equality rather than literal
record equality. -/
theorem rate_congr {bits : ℕ} {left right : CompatibilityRows}
    (hpooled : weightedEntropyList bits left.pooled =
      weightedEntropyList bits right.pooled)
    (hfirst : (left.first.map (weightedEntropyList bits)).sum =
      (right.first.map (weightedEntropyList bits)).sum)
    (hgroups : (left.groups.map (weightedEntropyList bits)).sum =
      (right.groups.map (weightedEntropyList bits)).sum) :
    left.rate bits = right.rate bits := by
  unfold rate
  rw [hpooled, hfirst, hgroups]

/-- The empty compatibility system has zero retained-rate contribution.  Besides being a useful
normalization law, this is the tiny semantic client for the list-based row interface. -/
@[simp] theorem rate_empty (bits : ℕ) :
    (CompatibilityRows.mk [] [] []).rate bits = 0 := by
  simp [rate, weightedEntropyList, entropyList, entropyTerm_zero]

end CompatibilityRows

end

end MatrixMultiplication.SimplifiedExponentRootRecurrence
