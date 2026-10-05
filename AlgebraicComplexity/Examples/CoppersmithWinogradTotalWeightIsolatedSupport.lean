/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightQuotientCompatibility
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationInjective

/-!
# Lossless total-weight compatibility cleanup on a leg-isolated family

At the total-weight quotient, a supported compatibility predicate is rigid: a compatible `Y`
label is the candidate's actual `Y` word, and similarly for `Z`.  Consequently, if the family
entering a compatibility pass is already injective on that leg, the pass deletes nothing.

This is an exact finite theorem.  It introduces no asymptotic estimate and does not assume a
tensor restriction.  Its two incidence corollaries show that the generic compatibility-counting
budget can be instantiated by zero on such a family.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- A supported total-weight `Y` compatibility pass is the identity on a `Y`-injective family. -/
theorem cwTotalWeightYIsolatedSupport_eq_ambient_of_injOn
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsYWeightSupported)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) ambient) :
    cwTotalWeightYIsolatedSupport depth n partAt rawTargets ambient = ambient := by
  exact compatibilityIsolatedSupport_eq_ambient_of_injOn_of_rigid
    ambient .Y (cwTotalWeightCompatibilityY depth n partAt rawTargets) hY
      (fun label address hcompatible ↦
        cwTotalWeight_label_eq_Y_of_featureCompatibleY
          depth n partAt rawTargets hsupported label address hcompatible)

/-- A supported total-weight `Z` compatibility pass is the identity on a `Z`-injective family. -/
theorem cwTotalWeightZIsolatedSupport_eq_ambient_of_injOn
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsZWeightSupported)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Z) ambient) :
    compatibilityIsolatedSupport ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets) = ambient := by
  exact compatibilityIsolatedSupport_eq_ambient_of_injOn_of_rigid
    ambient .Z (cwTotalWeightCompatibilityZ depth n partAt rawTargets) hZ
      (fun label address hcompatible ↦
        cwTotalWeight_label_eq_Z_of_featureCompatibleZ
          depth n partAt rawTargets hsupported label address hcompatible)

/-- If both visible legs are injective, the sequential `Y/Z` total-weight cleanup retains the
entire ambient family. -/
theorem cwTotalWeightYZIsolatedSupport_eq_ambient_of_injOn
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) ambient)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Z) ambient) :
    cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient = ambient := by
  rw [cwTotalWeightYZIsolatedSupport,
    cwTotalWeightYIsolatedSupport_eq_ambient_of_injOn
      depth n partAt rawTargets hsupported.2.1 ambient hY]
  exact cwTotalWeightZIsolatedSupport_eq_ambient_of_injOn
    depth n partAt rawTargets hsupported.2.2 ambient hZ

/-- A supported, `Y`-injective total-weight family has zero directed `Y` competitor incidence. -/
theorem cwTotalWeightYCompetitorIncidence_eq_zero_of_injOn
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsYWeightSupported)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) ambient) :
    cwTotalWeightYCompetitorIncidence depth n partAt rawTargets ambient = 0 := by
  exact compatibilityCompetitorIncidence_eq_zero_of_injOn_of_rigid
    ambient .Y (cwTotalWeightCompatibilityY depth n partAt rawTargets) hY
      (fun label address hcompatible ↦
        cwTotalWeight_label_eq_Y_of_featureCompatibleY
          depth n partAt rawTargets hsupported label address hcompatible)

/-- If both visible legs are injective, the post-`Y` directed `Z` competitor incidence is also
zero. -/
theorem cwTotalWeightZCompetitorIncidence_eq_zero_of_injOn
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) ambient)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Z) ambient) :
    cwTotalWeightZCompetitorIncidence depth n partAt rawTargets ambient = 0 := by
  rw [cwTotalWeightZCompetitorIncidence,
    cwTotalWeightYIsolatedSupport_eq_ambient_of_injOn
      depth n partAt rawTargets hsupported.2.1 ambient hY]
  exact compatibilityCompetitorIncidence_eq_zero_of_injOn_of_rigid
    ambient .Z (cwTotalWeightCompatibilityZ depth n partAt rawTargets) hZ
      (fun label address hcompatible ↦
        cwTotalWeight_label_eq_Z_of_featureCompatibleZ
          depth n partAt rawTargets hsupported.2.2 label address hcompatible)

/-- The old half-budget packaging is automatic, with both budgets equal to zero, on a
leg-isolated total-weight family. -/
theorem cwTotalWeight_card_ambient_le_two_mul_card_YZIsolatedSupport_of_injOn
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) ambient)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Z) ambient) :
    ambient.card ≤
      2 * (cwTotalWeightYZIsolatedSupport
        depth n partAt rawTargets ambient).card := by
  rw [cwTotalWeightYZIsolatedSupport_eq_ambient_of_injOn
    depth n partAt rawTargets hsupported ambient hY hZ]
  omega

end AlgebraicComplexity.Examples
