/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRows4
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion4Branch1TermsPart0
import MatrixMultiplication.Generated.TotalQuotientOuterFloorRootRegion4Branch1TermsPart1
import MatrixMultiplication.TotalQuotientExponentOuterFloorBridge

/-!
# Directed floor certificate: root orientation 4, branch 1

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
The 17 bounded shards of the companion `Terms` module are the bounded source slices of the exact
branch form the committed `rootBranchForm` computes from the emitted root rows, and their summed
lower-bound certificate clears the generated six-decimal regional floor.

The semantic-handoff caveat recorded on `TotalQuotientOuterFloorRootRows4` applies verbatim: the emitted rows
are a generated encoding of the certificate's root law, and identifying them with the
reconstruction from the committed `TotalQuotientPrimary*` tables is a separate, still-open
obligation — open in exactly the same way for the committed level-four analytic payload, whose
`branchRate` also reads generated cached tables.  The root side is not stronger.
-/

namespace MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region4.Branch1

open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
open MatrixMultiplication.TotalQuotientExponentOuterFloorBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

/-- The exact branch form the committed recurrence computes from the emitted rows. -/
def expectedRaw : Form :=
  (rootBranchForm 20 116 (rootCoordinate 0) (rootCoordinate 1)
    (rootCoordinate 2) MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Rows4.rows 1).2

/-- The branch denominator the recurrence pairs with that form. -/
theorem expectedBits :
    (rootBranchForm 20 116 (rootCoordinate 0) (rootCoordinate 1)
      (rootCoordinate 2) MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Rows4.rows 1).1 = 116 := by
  rfl

/-- Source-order raw shard forms. -/
def rawForms : List Form := [TermShard0.rawForm, TermShard1.rawForm, TermShard2.rawForm, TermShard3.rawForm, TermShard4.rawForm, TermShard5.rawForm, TermShard6.rawForm, TermShard7.rawForm, TermShard8.rawForm, TermShard9.rawForm, TermShard10.rawForm, TermShard11.rawForm, TermShard12.rawForm, TermShard13.rawForm, TermShard14.rawForm, TermShard15.rawForm, TermShard16.rawForm]

/-- Power-normalized shard forms. -/
def expectedForms : List Form := [TermShard0.form, TermShard1.form, TermShard2.form, TermShard3.form, TermShard4.form, TermShard5.form, TermShard6.form, TermShard7.form, TermShard8.form, TermShard9.form, TermShard10.form, TermShard11.form, TermShard12.form, TermShard13.form, TermShard14.form, TermShard15.form, TermShard16.form]

/-- Bounded shard certificates. -/
noncomputable def expectedCertificates : List (LowerBound 116) :=
  [TermShard0.certificate, TermShard1.certificate, TermShard2.certificate, TermShard3.certificate, TermShard4.certificate, TermShard5.certificate, TermShard6.certificate, TermShard7.certificate, TermShard8.certificate, TermShard9.certificate, TermShard10.certificate, TermShard11.certificate, TermShard12.certificate, TermShard13.certificate, TermShard14.certificate, TermShard15.certificate, TermShard16.certificate]

/-- Compositional lower certificate assembled from the bounded shards. -/
noncomputable def certificate : LowerBound 116 :=
  LowerBound.sum expectedCertificates

/-- The exact source form has the serialized number of logarithmic terms. -/
theorem expectedRaw_terms_length : expectedRaw.terms.length = 1045 := by rfl

/-- The exact source form carries no independent rational constant. -/
theorem expectedRaw_constant : expectedRaw.constantNumerator = 0 := by rfl

/-- Bounded source slice represented by raw shard 0. -/
theorem rawTermChunk0_eq :
    TermShard0.rawForm.terms = (expectedRaw.terms).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 1. -/
theorem rawTermChunk1_eq :
    TermShard1.rawForm.terms = ((expectedRaw.terms).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 2. -/
theorem rawTermChunk2_eq :
    TermShard2.rawForm.terms = (((expectedRaw.terms).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 3. -/
theorem rawTermChunk3_eq :
    TermShard3.rawForm.terms = ((((expectedRaw.terms).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 4. -/
theorem rawTermChunk4_eq :
    TermShard4.rawForm.terms = (((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 5. -/
theorem rawTermChunk5_eq :
    TermShard5.rawForm.terms = ((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 6. -/
theorem rawTermChunk6_eq :
    TermShard6.rawForm.terms = (((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 7. -/
theorem rawTermChunk7_eq :
    TermShard7.rawForm.terms = ((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 8. -/
theorem rawTermChunk8_eq :
    TermShard8.rawForm.terms = (((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 9. -/
theorem rawTermChunk9_eq :
    TermShard9.rawForm.terms = ((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 10. -/
theorem rawTermChunk10_eq :
    TermShard10.rawForm.terms = (((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 11. -/
theorem rawTermChunk11_eq :
    TermShard11.rawForm.terms = ((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 12. -/
theorem rawTermChunk12_eq :
    TermShard12.rawForm.terms = (((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 13. -/
theorem rawTermChunk13_eq :
    TermShard13.rawForm.terms = ((((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 14. -/
theorem rawTermChunk14_eq :
    TermShard14.rawForm.terms = (((((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 15. -/
theorem rawTermChunk15_eq :
    TermShard15.rawForm.terms = ((((((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 64 := by
  rfl

/-- Bounded source slice represented by raw shard 16. -/
theorem rawTermChunk16_eq :
    TermShard16.rawForm.terms = (((((((((((((((((expectedRaw.terms).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).drop 64).take 21 := by
  rfl

/-- The bounded raw shards concatenate to the exact source form. -/
theorem rawForms_sum_eq : Form.sum rawForms = expectedRaw := by rfl

/-- The certificate's exact form is the sum of the normalized shard forms.

Definitional: `LowerBound.reorder` installs each shard's normalized form verbatim, so the summed
certificate's form and the sum of the shard forms have the same normal form. -/
theorem certificate_form : certificate.form = Form.sum expectedForms := rfl

/-- The normalized shard sum evaluates to the exact source form. -/
theorem expectedForms_eval :
    Form.eval 116 (Form.sum expectedForms) =
      Form.eval 116 expectedRaw := by
  rw [← rawForms_sum_eq, Form.eval_sum, Form.eval_sum]
  simp only [expectedForms, rawForms, List.map, List.sum_cons, List.sum_nil,
    TermShard0.form,
    TermShard1.form,
    TermShard2.form,
    TermShard3.form,
    TermShard4.form,
    TermShard5.form,
    TermShard6.form,
    TermShard7.form,
    TermShard8.form,
    TermShard9.form,
    TermShard10.form,
    TermShard11.form,
    TermShard12.form,
    TermShard13.form,
    TermShard14.form,
    TermShard15.form,
    TermShard16.form,
    Form.eval_normalizePowersOfTwo]

/-- Directed regional endpoint obtained by adding the rational shard endpoints. -/
noncomputable def lower : ℝ := 18920664991209148937938779 / 9007199254740992000000000000

/-- The stated endpoint is the assembled certificate's endpoint. -/
theorem lower_eq_certificate_lower : lower = certificate.lower := by
  rw [certificate, LowerBound.sum_lower]
  simp only [expectedCertificates, List.map, List.sum_cons, List.sum_nil,
    TermShard0.certificate_lower,
    TermShard1.certificate_lower,
    TermShard2.certificate_lower,
    TermShard3.certificate_lower,
    TermShard4.certificate_lower,
    TermShard5.certificate_lower,
    TermShard6.certificate_lower,
    TermShard7.certificate_lower,
    TermShard8.certificate_lower,
    TermShard9.certificate_lower,
    TermShard10.certificate_lower,
    TermShard11.certificate_lower,
    TermShard12.certificate_lower,
    TermShard13.certificate_lower,
    TermShard14.certificate_lower,
    TermShard15.certificate_lower,
    TermShard16.certificate_lower]
  norm_num [lower,
    TermShard0.lower, TermShard0.constantNumerator, TermShard0.bits, TermShard0.positiveFloor, TermShard0.negativeCeiling,
    TermShard1.lower, TermShard1.constantNumerator, TermShard1.bits, TermShard1.positiveFloor, TermShard1.negativeCeiling,
    TermShard2.lower, TermShard2.constantNumerator, TermShard2.bits, TermShard2.positiveFloor, TermShard2.negativeCeiling,
    TermShard3.lower, TermShard3.constantNumerator, TermShard3.bits, TermShard3.positiveFloor, TermShard3.negativeCeiling,
    TermShard4.lower, TermShard4.constantNumerator, TermShard4.bits, TermShard4.positiveFloor, TermShard4.negativeCeiling,
    TermShard5.lower, TermShard5.constantNumerator, TermShard5.bits, TermShard5.positiveFloor, TermShard5.negativeCeiling,
    TermShard6.lower, TermShard6.constantNumerator, TermShard6.bits, TermShard6.positiveFloor, TermShard6.negativeCeiling,
    TermShard7.lower, TermShard7.constantNumerator, TermShard7.bits, TermShard7.positiveFloor, TermShard7.negativeCeiling,
    TermShard8.lower, TermShard8.constantNumerator, TermShard8.bits, TermShard8.positiveFloor, TermShard8.negativeCeiling,
    TermShard9.lower, TermShard9.constantNumerator, TermShard9.bits, TermShard9.positiveFloor, TermShard9.negativeCeiling,
    TermShard10.lower, TermShard10.constantNumerator, TermShard10.bits, TermShard10.positiveFloor, TermShard10.negativeCeiling,
    TermShard11.lower, TermShard11.constantNumerator, TermShard11.bits, TermShard11.positiveFloor, TermShard11.negativeCeiling,
    TermShard12.lower, TermShard12.constantNumerator, TermShard12.bits, TermShard12.positiveFloor, TermShard12.negativeCeiling,
    TermShard13.lower, TermShard13.constantNumerator, TermShard13.bits, TermShard13.positiveFloor, TermShard13.negativeCeiling,
    TermShard14.lower, TermShard14.constantNumerator, TermShard14.bits, TermShard14.positiveFloor, TermShard14.negativeCeiling,
    TermShard15.lower, TermShard15.constantNumerator, TermShard15.bits, TermShard15.positiveFloor, TermShard15.negativeCeiling,
    TermShard16.lower, TermShard16.constantNumerator, TermShard16.bits, TermShard16.positiveFloor, TermShard16.negativeCeiling]

/-- The generated six-decimal regional floor is below the compact directed endpoint. -/
theorem floor_le_lower : rootFloor ⟨4, by decide⟩ ≤ lower := by
  norm_num [rootFloor, rootFloorNumerators, denominator, lower]

/-- **The directed floor certificate of this root branch**, in the seam's shape. -/
noncomputable def branchFloorCertificate :
    BranchFloorCertificate 116 (rootFloor ⟨4, by decide⟩)
      (rootBranchRate 20 116 (rootCoordinate 0) (rootCoordinate 1)
        (rootCoordinate 2) MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Rows4.rows 1) where
  forms := expectedForms
  certificate := certificate
  lower := lower
  certificate_form := certificate_form
  lower_eq_certificate_lower := lower_eq_certificate_lower
  floor_le_lower := floor_le_lower
  rate_eq := by
    rw [expectedForms_eval]
    exact (rootBranchForm_eval 20 116 (rootCoordinate 0)
      (rootCoordinate 1) (rootCoordinate 2) MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Rows4.rows 1).symm

/-- The generated regional floor is below the exact reconstructed branch rate. -/
theorem floor_le_rate :
    rootFloor ⟨4, by decide⟩ ≤
      rootBranchRate 20 116 (rootCoordinate 0) (rootCoordinate 1)
        (rootCoordinate 2) MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Rows4.rows 1 :=
  branchFloorCertificate.floor_le_rate

end MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region4.Branch1
