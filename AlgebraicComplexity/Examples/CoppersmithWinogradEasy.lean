/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.PartitionedExtraction

/-!
# The three-constituent Coppersmith--Winograd easy tensor

Section 4.1 of He and Williams's CS 6810 matrix-multiplication notes starts the laser method with
the tensor formed by the `(0,1,1)`, `(1,0,1)`, and `(1,1,0)` constituents.  This file realizes
that tensor as an actual three-block partition, proves that the full `CW_q` tensor restricts to
it, transfers the constructive `q + 2` border-rank certificate, and packages its three
matrix-multiplication constituents.

The ambient block family is shared with the full CW client; the unused `last` block does not occur
in the recorded support.  This makes the easy tensor a literal variable-zeroing of the already
verified full tensor and avoids duplicating its polynomial certificate.

Source: [He and Williams, CS 6810 notes, Section 4.1](https://www.cs.cornell.edu/courses/cs6810/2023fa/Matrix.pdf).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The three middle addresses of the full CW support. -/
def easyBlockSupport : Finset CWBlockAddress := {cw011, cw101, cw110}

private theorem cw011_not_mem_easy_tail :
    cw011 ∉ ({cw101, cw110} : Finset CWBlockAddress) := by
  decide

private theorem cw101_ne_cw110_easy : cw101 ≠ cw110 := by
  decide

/-- Expand a sum over the three easy-support addresses. -/
theorem sum_easyBlockSupport {M : Type*} [AddCommMonoid M]
    (f : CWBlockAddress → M) :
    ∑ s ∈ easyBlockSupport, f s = f cw011 + (f cw101 + f cw110) := by
  unfold easyBlockSupport
  rw [Finset.sum_insert cw011_not_mem_easy_tail,
    Finset.sum_insert (by simpa using cw101_ne_cw110_easy)]
  simp

/-- Expand a product over the three easy-support addresses. -/
theorem prod_easyBlockSupport {M : Type*} [CommMonoid M]
    (f : CWBlockAddress → M) :
    ∏ s ∈ easyBlockSupport, f s = f cw011 * (f cw101 * f cw110) := by
  unfold easyBlockSupport
  rw [Finset.prod_insert cw011_not_mem_easy_tail,
    Finset.prod_insert (by simpa using cw101_ne_cw110_easy)]
  simp

/-- The easy support is a subfamily of the six-address CW support. -/
theorem easyBlockSupport_subset_cwBlockSupport : easyBlockSupport ⊆ cwBlockSupport := by
  decide

@[simp] theorem card_easyBlockSupport : easyBlockSupport.card = 3 := by
  decide

/-- Keep exactly the zero and middle variable blocks. -/
def easyKeepBlock (_ : Leg) (a : CWBlock) : Prop := a ≠ .last

instance easyKeepBlock_decidable (c : Leg) (a : CWBlock) :
    Decidable (easyKeepBlock c a) := by
  unfold easyKeepBlock
  infer_instance

/-- Filtering the full CW support by the two easy block labels leaves exactly the three middle
addresses. -/
theorem cwBlockSupport_filter_easyKeepBlock :
    cwBlockSupport.filter (fun s ↦ ∀ c, easyKeepBlock c (s c)) = easyBlockSupport := by
  decide

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- The typed three-constituent easy tensor.  This thin `withSupport` wrapper is reducible so the
support subtype is transparently the stable public type `easyBlockSupport`. -/
@[reducible] noncomputable def easyPartitionedTensor :
    PartitionedTensor (K := K) (A := fun _ : Leg ↦ CWBlock)
      (CWPartitionBlockSpace K q) :=
  (cwPartitionedTensor K q).withSupport easyBlockSupport

@[simp] theorem easyPartitionedTensor_support :
    (easyPartitionedTensor K q).support = easyBlockSupport := rfl

@[simp] theorem easyPartitionedTensor_constituent (s : CWBlockAddress) :
    (easyPartitionedTensor K q).constituent s = cwPartitionConstituent K q s := rfl

/-- Variable zeroing of the three final-coordinate blocks restricts the full CW realization to
the easy tensor. -/
theorem cwPartitionedTensor_restricts_easy :
    Restricts (cwPartitionedTensor K q).realize (easyPartitionedTensor K q).realize := by
  have h := Restricts.partitionedSelect
    (cwPartitionedTensor K q) (easyKeepBlock : ∀ _ : Leg, CWBlock → Prop)
  have hsupport :
      ((cwPartitionedTensor K q).select
        (easyKeepBlock : ∀ _ : Leg, CWBlock → Prop)).support = easyBlockSupport := by
    change cwBlockSupport.filter (fun s ↦ ∀ c, easyKeepBlock c (s c)) = easyBlockSupport
    exact cwBlockSupport_filter_easyKeepBlock
  refine h.trans (Restricts.of_eq ?_)
  unfold PartitionedTensor.realize easyPartitionedTensor PartitionedTensor.withSupport
  rw [hsupport]
  rfl

/-- The classical constructive easy-tensor border-rank certificate has length `q + 2`. -/
theorem easyPartitionedTensor_borderRankLE :
    BorderRankLE (q + 2) (easyPartitionedTensor K q).realize := by
  have hfull : BorderRankLE (q + 2) (cwPartitionedTensor K q).realize :=
    (BorderRankLE.isomorphic (cwPartitionedTensor_isomorphic K q)).mpr
      (coppersmithWinograd_borderRankLE K q)
  exact hfull.of_restricts (cwPartitionedTensor_restricts_easy K q)

theorem easyPartitionedTensor_borderRank_le :
    borderRank (easyPartitionedTensor K q).realize ≤ q + 2 :=
  borderRank_le_iff.mpr (easyPartitionedTensor_borderRankLE K q)

/-- The three-address easy support remains tight under the standard CW block weights. -/
theorem easyBlockSupport_isTight : IsTightSupport easyBlockSupport := by
  refine ⟨fun _ ↦ cwBlockWeight, fun _ ↦ cwBlockWeight_injective, 2, ?_⟩
  intro s hs
  exact cwBlockSupport_weight_sum s (easyBlockSupport_subset_cwBlockSupport hs)

/-- Exact constituent certificate underlying the easy tensor's polynomial-degeneration
certificate.  Keeping the stronger statement available lets finite extraction clients assemble
componentwise restrictions without synchronizing polynomial leading degrees. -/
theorem easySupportedConstituent_restricts
    (s : (easyPartitionedTensor K q).support) :
    Restricts ((easyPartitionedTensor K q).constituent s.1)
      (matrixMultiplication (K := K)
        (cwConstituentDimensions q s.1).1
        (cwConstituentDimensions q s.1).2.1
        (cwConstituentDimensions q s.1).2.2) := by
  change Restricts (cwPartitionConstituent K q s.1)
    (matrixMultiplication (K := K)
      (cwConstituentDimensions q s.1).1
      (cwConstituentDimensions q s.1).2.1
      (cwConstituentDimensions q s.1).2.2)
  exact cwSupportedConstituent_restricts K q
    ⟨s.1, easyBlockSupport_subset_cwBlockSupport s.2⟩

/-- Every easy constituent is one of the three volume-`q` rectangular matrix-multiplication
tensors. -/
noncomputable def easyPartitionedMMCertificate (hq : 0 < q) :
    PartitionedMMCertificate K (easyPartitionedTensor K q) where
  m s := (cwConstituentDimensions q s.1).1
  n s := (cwConstituentDimensions q s.1).2.1
  p s := (cwConstituentDimensions q s.1).2.2
  m_pos s := by
    let t : cwBlockSupport :=
      ⟨s.1, easyBlockSupport_subset_cwBlockSupport s.2⟩
    exact (cwConstituentDimensions_pos q hq t).1
  n_pos s := by
    let t : cwBlockSupport :=
      ⟨s.1, easyBlockSupport_subset_cwBlockSupport s.2⟩
    exact (cwConstituentDimensions_pos q hq t).2.1
  p_pos s := by
    let t : cwBlockSupport :=
      ⟨s.1, easyBlockSupport_subset_cwBlockSupport s.2⟩
    exact (cwConstituentDimensions_pos q hq t).2.2
  degenerates s := by
    apply PolynomialDegenerates.of_restricts
    exact easySupportedConstituent_restricts K q s

/-- Every supported easy constituent has volume exactly `q`. -/
theorem easyPartitionedMMCertificate_volume (hq : 0 < q)
    (s : (easyPartitionedTensor K q).support) :
    (easyPartitionedMMCertificate K q hq).volume s = q := by
  rcases s with ⟨s, hs⟩
  simp only [easyPartitionedTensor_support, easyBlockSupport,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;>
    simp [PartitionedMMCertificate.volume, easyPartitionedMMCertificate,
      cwConstituentDimensions]

end

end AlgebraicComplexity.Examples
