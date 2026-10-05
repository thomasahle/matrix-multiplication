/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightIsolatedSupport

set_option autoImplicit false

/-!
# Counting one present fixed full-cell family

The present total-weight route first retains an actually supported marked family whose `Y` labels
are injective.  It then selects one full tagged empirical cell type and performs the paper's
`Y/Z` compatibility cleanup.  This file packages the exact loss in that order:

* selecting the full cell type costs only the standard polynomial number of empirical types;
* inherited `Y`-injectivity and total-weight rigidity make the `Y` incidence exactly zero; and
* the only remaining finite loss is the literal directed `Z`-competitor incidence in that cell.

No tensor relation, entropy estimate, missing-family bound, or certificate-specific array occurs
in these statements.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- One present full tagged cell has polynomially comparable size, up to precisely the surviving
`Y/Z` support and its directed `Z`-competitor incidence.

The `Y` term from the generic two-pass union bound disappears rather than being bounded: the
selected cell is a subfamily of the already `Y`-injective present marked family. -/
theorem exists_reference_card_le_fullCellLoss_mul_card_YZ_add_ZIncidence
    {Part : Type u} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (sigma : Orientation)
    (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsYWeightSupported)
    (present : Finset
      (BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hpresent : present.Nonempty)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y)
      present) :
    ∃ reference ∈ present,
      present.card ≤
        (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
          ((cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
              (cwFixedTargetCellTypeCoarseSupport
                depth n partAt sigma present reference)).card +
            cwTotalWeightZCompetitorIncidence depth n partAt rawTargets
              (cwFixedTargetCellTypeCoarseSupport
                depth n partAt sigma present reference)) := by
  classical
  obtain ⟨reference, hreference, hselect⟩ :=
    exists_reference_card_le_polynomial_mul_fixedTargetCellType
      depth n partAt sigma present hpresent
  let fixed := cwFixedTargetCellTypeCoarseSupport
    depth n partAt sigma present reference
  have hfixedSubset : fixed ⊆ present := by
    intro address haddress
    exact ((mem_cwFixedTargetCellTypeCoarseSupport_iff
      depth n partAt sigma present reference address).mp haddress).1
  have hfixedY : Set.InjOn
      (fun address : BlockAddress
        (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y)
      fixed := by
    intro first hfirst second hsecond heq
    exact hY (hfixedSubset hfirst) (hfixedSubset hsecond) heq
  have hyZero : cwTotalWeightYCompetitorIncidence
      depth n partAt rawTargets fixed = 0 :=
    cwTotalWeightYCompetitorIncidence_eq_zero_of_injOn
      depth n partAt rawTargets hsupported fixed hfixedY
  have hcleanup : fixed.card ≤
      (cwTotalWeightYZIsolatedSupport
          depth n partAt rawTargets fixed).card +
        cwTotalWeightZCompetitorIncidence depth n partAt rawTargets fixed := by
    have hcount := cwTotalWeight_card_ambient_le_card_YZIsolatedSupport_add_incidences
      depth n partAt rawTargets fixed
    simpa only [hyZero, Nat.add_zero] using hcount
  refine ⟨reference, hreference, ?_⟩
  simpa only [fixed] using hselect.trans
    (Nat.mul_le_mul_left
      ((n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth)) hcleanup)

/-- Half-budget form of
`exists_reference_card_le_fullCellLoss_mul_card_YZ_add_ZIncidence`.

If the directed `Z` incidence consumes at most half of every candidate full cell, one selected
cell retains at least its polynomially scaled half.  The universal hypothesis reflects the order
of choice: the largest empirical cell is selected before its `Z` incidence is evaluated. -/
theorem exists_reference_card_le_two_mul_fullCellLoss_mul_card_YZ
    {Part : Type u} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (sigma : Orientation)
    (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsYWeightSupported)
    (present : Finset
      (BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hpresent : present.Nonempty)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y)
      present)
    (hZhalf : ∀ reference ∈ present,
      2 * cwTotalWeightZCompetitorIncidence depth n partAt rawTargets
          (cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma present reference) ≤
        (cwFixedTargetCellTypeCoarseSupport
          depth n partAt sigma present reference).card) :
    ∃ reference ∈ present,
      present.card ≤
        2 * (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
          (cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (cwFixedTargetCellTypeCoarseSupport
              depth n partAt sigma present reference)).card := by
  classical
  obtain ⟨reference, hreference, hselect⟩ :=
    exists_reference_card_le_polynomial_mul_fixedTargetCellType
      depth n partAt sigma present hpresent
  let fixed := cwFixedTargetCellTypeCoarseSupport
    depth n partAt sigma present reference
  have hfixedSubset : fixed ⊆ present := by
    intro address haddress
    exact ((mem_cwFixedTargetCellTypeCoarseSupport_iff
      depth n partAt sigma present reference address).mp haddress).1
  have hfixedY : Set.InjOn
      (fun address : BlockAddress
        (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y)
      fixed := by
    intro first hfirst second hsecond heq
    exact hY (hfixedSubset hfirst) (hfixedSubset hsecond) heq
  have hyZero : cwTotalWeightYCompetitorIncidence
      depth n partAt rawTargets fixed = 0 :=
    cwTotalWeightYCompetitorIncidence_eq_zero_of_injOn
      depth n partAt rawTargets hsupported fixed hfixedY
  have hfixedHalf : 2 * (0 + cwTotalWeightZCompetitorIncidence
      depth n partAt rawTargets fixed) ≤ fixed.card := by
    simpa only [fixed, Nat.zero_add] using hZhalf reference hreference
  have hcleanup : fixed.card ≤
      2 * (cwTotalWeightYZIsolatedSupport
        depth n partAt rawTargets fixed).card :=
    cwTotalWeight_card_ambient_le_two_mul_card_YZIsolatedSupport
      depth n partAt rawTargets fixed 0
        (cwTotalWeightZCompetitorIncidence depth n partAt rawTargets fixed)
      (le_of_eq hyZero) le_rfl hfixedHalf
  refine ⟨reference, hreference, ?_⟩
  calc
    present.card ≤
        (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) * fixed.card :=
      hselect
    _ ≤ (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
        (2 * (cwTotalWeightYZIsolatedSupport
          depth n partAt rawTargets fixed).card) :=
      Nat.mul_le_mul_left _ hcleanup
    _ = 2 * (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
        (cwTotalWeightYZIsolatedSupport
          depth n partAt rawTargets fixed).card := by
      ac_rfl
    _ = 2 * (n + 2) ^ Fintype.card (CWOrientedCoarseCell Part depth) *
        (cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
          (cwFixedTargetCellTypeCoarseSupport
            depth n partAt sigma present reference)).card := by
      rfl

end AlgebraicComplexity.Examples
