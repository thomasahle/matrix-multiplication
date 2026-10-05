/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropyForm
import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualCore

set_option autoImplicit false

/-!
# Exact forms for support-restricted conditional integer duals

The A5 certificate assigns a dyadic source count `c u`, a logical parent coordinate `z u`, and a
positive integer score `w u` to every legal child state.  Its row partition is the restricted sum

`P z = ∑ u, if coord u = z then w u else 0`.

This module packages the resulting mass-weighted conditional dual as a
`SignedDyadicLogForm.Form`.  Subtracting that dual from the source homogeneous entropy evaluates
exactly to

`D log₂ D - ∑ u, c u log₂ (c u) + ∑ u, c u log₂ (w u)
  - ∑ z, c_z log₂ (P z)`,

all divided by the common dyadic denominator.  In particular, no parent entropy `H(Z)` and no
unrestricted state partition are inserted by the exact-form layer.

This transcribes the finite integer-potential evaluation step of the Total-Weight manuscript,
`better_bound/paper.tex`, `sec:dual`, Proposition `prop:dual` (lines 2286–2307 in the 2026-09-06
draft), separately on each fixed-coordinate support fiber. Its combination-loss application is
[alman2025more], `papers/sources/2404.16349/constituent.tex:113-147`. The actual entropy bound is
proved in the imported core; this module proves only its exact signed-log representation.
-/

open scoped BigOperators

namespace MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDual

noncomputable section

universe u v

/-- One positively weighted base-two logarithm in a common dyadic form. -/
def positiveLogTermForm (coefficient argument : ℕ) : Form :=
  { constantNumerator := 0
    terms := [⟨argument, (coefficient : ℤ)⟩] }

/-- Evaluating one positively weighted logarithm form gives its dyadic mass times the base-two
logarithm of its argument. -/
theorem positiveLogTermForm_eval (bits coefficient argument : ℕ) :
    Form.eval bits (positiveLogTermForm coefficient argument) =
      mass bits coefficient * SignedDyadicLogForm.log2Nat argument := by
  simp [positiveLogTermForm, Form.eval, Form.termsValue, Form.termValue, mass]

/-- Canonical finite serialization of the source-state numerators. -/
def sourceNumerators {U : Type u} [Fintype U] (numerator : U → ℕ) : List ℕ :=
  (Finset.univ : Finset U).toList.map numerator

/-- Homogeneous entropy form of the source-state count row. -/
def sourceEntropyForm {U : Type u} [Fintype U]
    (bits : ℕ) (numerator : U → ℕ) : Form :=
  weightedEntropyForm bits (sourceNumerators numerator)

/-- Evaluating the source-state entropy form gives the homogeneous entropy of the serialized
source-count row. -/
theorem sourceEntropyForm_eval {U : Type u} [Fintype U]
    (bits : ℕ) (numerator : U → ℕ) :
    Form.eval bits (sourceEntropyForm bits numerator) =
      weightedEntropyList bits (sourceNumerators numerator) := by
  exact weightedEntropyForm_eval bits (sourceNumerators numerator)

/-- Positive score-expectation terms, one for every child state. -/
def stateWeightForm {U : Type u} [Fintype U]
    (numerator weight : U → ℕ) : Form :=
  Form.sum ((Finset.univ : Finset U).toList.map fun state ↦
    positiveLogTermForm (numerator state) (weight state))

/-- Evaluating the score-expectation form gives the mass-weighted sum of the base-two logarithms
of the child-state scores. -/
theorem stateWeightForm_eval {U : Type u} [Fintype U]
    (bits : ℕ) (numerator weight : U → ℕ) :
    Form.eval bits (stateWeightForm numerator weight) =
      ∑ state, mass bits (numerator state) *
        SignedDyadicLogForm.log2Nat (weight state) := by
  rw [stateWeightForm, Form.eval_sum, List.map_map, Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro state _
  exact positiveLogTermForm_eval bits (numerator state) (weight state)

/-- Source mass in one logical-coordinate fiber.  This deliberately reuses the same filtered
integer sum as the support-restricted Gibbs partition. -/
def fixedCoordinateFiberNumerator
    {Z : Type u} {U : Type v} [DecidableEq Z] [Fintype U]
    (coord : U → Z) (numerator : U → ℕ) (z : Z) : ℕ :=
  fixedCoordinateIntegerFiberPartition coord numerator z

/-- The fiber numerator is, by definition, the coordinate-restricted sum of the source counts. -/
theorem fixedCoordinateFiberNumerator_eq
    {Z : Type u} {U : Type v} [DecidableEq Z] [Fintype U]
    (coord : U → Z) (numerator : U → ℕ) (z : Z) :
    fixedCoordinateFiberNumerator coord numerator z =
      ∑ state, if coord state = z then numerator state else 0 :=
  rfl

/-- Parent-weighted restricted partition terms. -/
def fixedCoordinatePartitionForm
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (coord : U → Z) (numerator weight : U → ℕ) : Form :=
  Form.sum ((Finset.univ : Finset Z).toList.map fun z ↦
    positiveLogTermForm
      (fixedCoordinateFiberNumerator coord numerator z)
      (fixedCoordinateIntegerFiberPartition coord weight z))

/-- Evaluating the restricted-partition form gives the fiberwise mass-weighted logarithms of the
support-restricted Gibbs partitions. -/
theorem fixedCoordinatePartitionForm_eval
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (bits : ℕ) (coord : U → Z) (numerator weight : U → ℕ) :
    Form.eval bits (fixedCoordinatePartitionForm coord numerator weight) =
      ∑ z, mass bits (fixedCoordinateFiberNumerator coord numerator z) *
        SignedDyadicLogForm.log2Nat
          (fixedCoordinateIntegerFiberPartition coord weight z) := by
  rw [fixedCoordinatePartitionForm, Form.eval_sum, List.map_map,
    Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro z _
  exact positiveLogTermForm_eval bits
    (fixedCoordinateFiberNumerator coord numerator z)
    (fixedCoordinateIntegerFiberPartition coord weight z)

/-- The mass-weighted support-restricted conditional dual: restricted partition logarithms minus
the score expectation. -/
def fixedCoordinateDualForm
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (coord : U → Z) (numerator weight : U → ℕ) : Form :=
  Form.sub (fixedCoordinatePartitionForm coord numerator weight)
    (stateWeightForm numerator weight)

/-- Evaluating the support-restricted conditional dual form gives those restricted partition
logarithms minus the score expectation. -/
theorem fixedCoordinateDualForm_eval
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (bits : ℕ) (coord : U → Z) (numerator weight : U → ℕ) :
    Form.eval bits (fixedCoordinateDualForm coord numerator weight) =
      (∑ z, mass bits (fixedCoordinateFiberNumerator coord numerator z) *
          SignedDyadicLogForm.log2Nat
            (fixedCoordinateIntegerFiberPartition coord weight z)) -
        ∑ state, mass bits (numerator state) *
          SignedDyadicLogForm.log2Nat (weight state) := by
  rw [fixedCoordinateDualForm, Form.eval_sub,
    fixedCoordinatePartitionForm_eval, stateWeightForm_eval]

/-- Exact retained-row form: source homogeneous entropy minus the support-restricted conditional
dual. -/
def retainedRowForm
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (bits : ℕ) (coord : U → Z) (numerator weight : U → ℕ) : Form :=
  Form.sub (sourceEntropyForm bits numerator)
    (fixedCoordinateDualForm coord numerator weight)

/-- Evaluation is literally the four-term signed expression checked by A5: source entropy,
positive score expectation, and negative restricted row partitions. -/
theorem retainedRowForm_eval
    {Z : Type u} {U : Type v} [Fintype Z] [DecidableEq Z] [Fintype U]
    (bits : ℕ) (coord : U → Z) (numerator weight : U → ℕ) :
    Form.eval bits (retainedRowForm bits coord numerator weight) =
      weightedEntropyList bits (sourceNumerators numerator) +
        (∑ state, mass bits (numerator state) *
          SignedDyadicLogForm.log2Nat (weight state)) -
        ∑ z, mass bits (fixedCoordinateFiberNumerator coord numerator z) *
          SignedDyadicLogForm.log2Nat
            (fixedCoordinateIntegerFiberPartition coord weight z) := by
  rw [retainedRowForm, Form.eval_sub, sourceEntropyForm_eval,
    fixedCoordinateDualForm_eval]
  ring

end

end MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm
