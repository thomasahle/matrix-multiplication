/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTightQuotientCore
import Mathlib.Order.Partition.Finpartition

/-!
# Classification of tight depth-one Coppersmith--Winograd quotients

A partition of the nine two-digit split words gives a canonical surjective quotient by sending a
word to its part.  The affine decoder in `CoppersmithWinogradTightQuotientCore` reduces tightness
of the resulting support to the kernel of one integer linear form.

There are exactly ten possible kernels.  The only arithmetic split below is over the two digit
differences, each in `[-2, 2]`; its 25 leaves identify the eight exceptional projective slopes.
If there is no collision, the kernel is discrete.  No partition Fintype is evaluated.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- The partition of the nine depth-one split words into fibers of an integer linear form. -/
noncomputable def cwLinearFinpartition (lambda mu : ℤ) :
    Finpartition (Finset.univ : Finset (SplitWord 1)) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker (cwSplitLinearForm lambda mu))

/-- The canonical quotient map associated to a partition of the nine depth-one split words. -/
noncomputable def cwFinpartitionQuotient
    (P : Finpartition (Finset.univ : Finset (SplitWord 1)))
    (word : SplitWord 1) : P.parts :=
  ⟨P.part word, P.part_mem.mpr (Finset.mem_univ word)⟩

@[simp] theorem cwFinpartitionQuotient_eq_iff
    (P : Finpartition (Finset.univ : Finset (SplitWord 1)))
    (left right : SplitWord 1) :
    cwFinpartitionQuotient P left = cwFinpartitionQuotient P right ↔
      P.part left = P.part right := by
  simp only [cwFinpartitionQuotient, Subtype.mk.injEq]

/-- Every part has a representative, so the canonical partition quotient is surjective. -/
theorem cwFinpartitionQuotient_surjective
    (P : Finpartition (Finset.univ : Finset (SplitWord 1))) :
    Function.Surjective (cwFinpartitionQuotient P) := by
  intro part
  obtain ⟨word, hword⟩ := P.nonempty_of_mem_parts part.2
  refine ⟨word, Subtype.ext ?_⟩
  exact P.part_eq_of_mem part.2 hword

/-- Use the same partition quotient independently on all three tensor legs. -/
noncomputable def cwSamePartitionQuotient
    (P : Finpartition (Finset.univ : Finset (SplitWord 1))) :
    ∀ _c : Leg, SplitWord 1 → P.parts :=
  fun _c ↦ cwFinpartitionQuotient P

/-- Image of the physical depth-one support under the same partition quotient on every leg. -/
noncomputable def cwSamePartitionQuotientSupport
    (P : Finpartition (Finset.univ : Finset (SplitWord 1))) :
    Finset (BlockAddress (fun _c ↦ P.parts)) :=
  cwDepthOneQuotientSupport (cwSamePartitionQuotient P)

private theorem cwSamePartitionQuotient_surjective
    (P : Finpartition (Finset.univ : Finset (SplitWord 1))) :
    ∀ c, Function.Surjective (cwSamePartitionQuotient P c) := by
  intro c
  exact cwFinpartitionQuotient_surjective P

/-- Two words lie in the same linear-form part exactly when the form has the same value. -/
@[simp] theorem cwLinearFinpartition_part_eq_part
    (lambda mu : ℤ) (left right : SplitWord 1) :
    (cwLinearFinpartition lambda mu).part left =
        (cwLinearFinpartition lambda mu).part right ↔
      cwSplitLinearForm lambda mu left = cwSplitLinearForm lambda mu right := by
  classical
  rw [← (cwLinearFinpartition lambda mu).mem_part_iff_part_eq_part
    (Finset.mem_univ left) (Finset.mem_univ right)]
  change left ∈
      (Finpartition.ofSetoid (Setoid.ker (cwSplitLinearForm lambda mu))).part right ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact eq_comm

private theorem finpartition_eq_of_part_rel
    {P Q : Finpartition (Finset.univ : Finset (SplitWord 1))}
    (hrel : ∀ left right, P.part left = P.part right ↔
      Q.part left = Q.part right) :
    P = Q := by
  have hpart (word : SplitWord 1) : P.part word = Q.part word := by
    apply Finset.ext
    intro other
    rw [P.mem_part_iff_part_eq_part
      (Finset.mem_univ other) (Finset.mem_univ word)]
    rw [Q.mem_part_iff_part_eq_part
      (Finset.mem_univ other) (Finset.mem_univ word)]
    exact hrel other word
  apply Finpartition.ext
  apply Finset.ext
  intro part
  constructor
  · intro hP
    obtain ⟨word, hword⟩ := P.nonempty_of_mem_parts hP
    have hp := P.part_eq_of_mem hP hword
    rw [← hp, hpart word]
    exact Q.part_mem.mpr (Finset.mem_univ word)
  · intro hQ
    obtain ⟨word, hword⟩ := Q.nonempty_of_mem_parts hQ
    have hq := Q.part_eq_of_mem hQ hword
    rw [← hq, ← hpart word]
    exact P.part_mem.mpr (Finset.mem_univ word)

/-- Tightness of a same-partition quotient is exactly equality with a linear-form partition. -/
theorem cwSamePartitionQuotientSupport_isTight_iff_eq_linear
    (P : Finpartition (Finset.univ : Finset (SplitWord 1))) :
    IsTightSupport (cwSamePartitionQuotientSupport P) ↔
      ∃ lambda mu : ℤ, P = cwLinearFinpartition lambda mu := by
  have hcore := cwDepthOneQuotientSupport_isTight_iff_fibers_linear
    (cwSamePartitionQuotient P) (cwSamePartitionQuotient_surjective P)
  constructor
  · intro htight
    obtain ⟨lambda, mu, hfibers⟩ := hcore.mp htight
    refine ⟨lambda, mu, finpartition_eq_of_part_rel ?_⟩
    intro left right
    have hP : P.part left = P.part right ↔
        cwSplitLinearForm lambda mu left = cwSplitLinearForm lambda mu right := by
      simpa only [cwSamePartitionQuotient, cwFinpartitionQuotient_eq_iff] using
        hfibers .X left right
    exact hP.trans (cwLinearFinpartition_part_eq_part lambda mu left right).symm
  · rintro ⟨lambda, mu, rfl⟩
    apply hcore.mpr
    refine ⟨lambda, mu, ?_⟩
    intro c left right
    simpa only [cwSamePartitionQuotient, cwFinpartitionQuotient_eq_iff] using
      cwLinearFinpartition_part_eq_part lambda mu left right

/-- The ten projective kernel types of integer linear forms on the ternary two-digit square. -/
inductive CWTightQuotientKind
  | constant
  | firstCoordinate
  | secondCoordinate
  | sum
  | difference
  | twoFirstPlusSecond
  | negativeTwoFirstPlusSecond
  | firstPlusTwoSecond
  | firstMinusTwoSecond
  | discrete
  deriving DecidableEq, Repr

instance : Fintype CWTightQuotientKind :=
  Fintype.ofList
    [.constant, .firstCoordinate, .secondCoordinate, .sum, .difference,
      .twoFirstPlusSecond, .negativeTwoFirstPlusSecond, .firstPlusTwoSecond,
      .firstMinusTwoSecond, .discrete]
    (by
      intro kind
      cases kind <;> simp)

namespace CWTightQuotientKind

/-- A normalized coefficient pair representing a tight quotient kind. -/
def coefficients : CWTightQuotientKind → ℤ × ℤ
  | .constant => (0, 0)
  | .firstCoordinate => (1, 0)
  | .secondCoordinate => (0, 1)
  | .sum => (1, 1)
  | .difference => (1, -1)
  | .twoFirstPlusSecond => (2, 1)
  | .negativeTwoFirstPlusSecond => (-2, 1)
  | .firstPlusTwoSecond => (1, 2)
  | .firstMinusTwoSecond => (1, -2)
  | .discrete => (3, 1)

/-- The canonical fiber partition represented by a normalized quotient kind. -/
noncomputable def partition (kind : CWTightQuotientKind) :
    Finpartition (Finset.univ : Finset (SplitWord 1)) :=
  cwLinearFinpartition kind.coefficients.1 kind.coefficients.2

end CWTightQuotientKind

private theorem cwSplitLinearForm_scale
    (k lambda mu : ℤ) (word : SplitWord 1) :
    cwSplitLinearForm (k * lambda) (k * mu) word =
      k * cwSplitLinearForm lambda mu word := by
  simp only [cwSplitLinearForm]
  ring

private theorem cwLinearFinpartition_eq_kind_of_scale
    (lambda mu k : ℤ) (kind : CWTightQuotientKind)
    (hk : k ≠ 0)
    (hlambda : lambda = k * kind.coefficients.1)
    (hmu : mu = k * kind.coefficients.2) :
    cwLinearFinpartition lambda mu = kind.partition := by
  apply finpartition_eq_of_part_rel
  intro left right
  rw [cwLinearFinpartition_part_eq_part, CWTightQuotientKind.partition,
    cwLinearFinpartition_part_eq_part, hlambda, hmu,
    cwSplitLinearForm_scale, cwSplitLinearForm_scale]
  constructor
  · exact mul_left_cancel₀ hk
  · intro h
    rw [h]

private theorem cwCoefficients_proportional_of_collision
    {lambda mu : ℤ} (hnotzero : ¬ (lambda = 0 ∧ mu = 0))
    {left right : SplitWord 1} (hne : left ≠ right)
    (hlinear : cwSplitLinearForm lambda mu left =
      cwSplitLinearForm lambda mu right) :
    ∃ kind : CWTightQuotientKind, ∃ k : ℤ,
      k ≠ 0 ∧ lambda = k * kind.coefficients.1 ∧
        mu = k * kind.coefficients.2 := by
  let da : ℤ := (left 0 : ℤ) - (right 0 : ℤ)
  let db : ℤ := (left 1 : ℤ) - (right 1 : ℤ)
  have hdaLower : -2 ≤ da := by
    dsimp only [da]
    omega
  have hdaUpper : da ≤ 2 := by
    dsimp only [da]
    omega
  have hdbLower : -2 ≤ db := by
    dsimp only [db]
    omega
  have hdbUpper : db ≤ 2 := by
    dsimp only [db]
    omega
  have hdifference : da ≠ 0 ∨ db ≠ 0 := by
    by_contra hzero
    have hda : da = 0 := by
      by_contra h
      exact hzero (Or.inl h)
    have hdb : db = 0 := by
      by_contra h
      exact hzero (Or.inr h)
    have hfirst : left 0 = right 0 := by
      apply Fin.ext
      dsimp only [da] at hda
      omega
    have hsecond : left 1 = right 1 := by
      apply Fin.ext
      dsimp only [db] at hdb
      omega
    apply hne
    calc
      left = cwSplitPair (left 0) (left 1) := (cwSplitPair_eta left).symm
      _ = cwSplitPair (right 0) (right 1) := by rw [hfirst, hsecond]
      _ = right := cwSplitPair_eta right
  have hrelation : lambda * da + mu * db = 0 := by
    dsimp only [cwSplitLinearForm] at hlinear
    dsimp only [da, db]
    linear_combination hlinear
  interval_cases da <;> interval_cases db
  all_goals first
    | omega
    | (refine ⟨.firstCoordinate, lambda, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)
    | (refine ⟨.secondCoordinate, mu, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)
    | (refine ⟨.sum, lambda, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)
    | (refine ⟨.difference, lambda, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)
    | (refine ⟨.twoFirstPlusSecond, mu, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)
    | (refine ⟨.negativeTwoFirstPlusSecond, mu, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)
    | (refine ⟨.firstPlusTwoSecond, lambda, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)
    | (refine ⟨.firstMinusTwoSecond, lambda, ?_, ?_, ?_⟩ <;>
        simp [CWTightQuotientKind.coefficients] <;> omega)

/-- The normalized `(3,1)` form is injective on the ternary two-digit square. -/
theorem cwSplitLinearForm_discrete_injective :
    Function.Injective (cwSplitLinearForm 3 1) := by
  intro left right heq
  have hfirst : left 0 = right 0 := by
    apply Fin.ext
    simp only [cwSplitLinearForm] at heq
    omega
  have hsecond : left 1 = right 1 := by
    apply Fin.ext
    simp only [cwSplitLinearForm] at heq
    omega
  funext position
  fin_cases position
  · exact hfirst
  · exact hsecond

/-- Every integer linear form on two ternary digits has one of the ten normalized kernels. -/
theorem cwLinearFinpartition_eq_kind (lambda mu : ℤ) :
    ∃ kind : CWTightQuotientKind,
      cwLinearFinpartition lambda mu = kind.partition := by
  by_cases hzero : lambda = 0 ∧ mu = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    exact ⟨.constant, rfl⟩
  by_cases hcollision : ∃ left right : SplitWord 1,
      left ≠ right ∧ cwSplitLinearForm lambda mu left =
        cwSplitLinearForm lambda mu right
  · obtain ⟨left, right, hne, hlinear⟩ := hcollision
    obtain ⟨kind, k, hk, hlambda, hmu⟩ :=
      cwCoefficients_proportional_of_collision hzero hne hlinear
    exact ⟨kind,
      cwLinearFinpartition_eq_kind_of_scale lambda mu k kind hk hlambda hmu⟩
  · refine ⟨.discrete, ?_⟩
    change cwLinearFinpartition lambda mu = cwLinearFinpartition 3 1
    apply finpartition_eq_of_part_rel
    intro left right
    rw [cwLinearFinpartition_part_eq_part, cwLinearFinpartition_part_eq_part]
    constructor
    · intro hlinear
      have heq : left = right := by
        by_contra hne
        exact hcollision ⟨left, right, hne, hlinear⟩
      rw [heq]
    · intro hlinear
      rw [cwSplitLinearForm_discrete_injective hlinear]

/-- The same-partition depth-one quotient is tight exactly for one of the ten normalized kinds. -/
theorem cwSamePartitionQuotientSupport_isTight_iff_kind
    (P : Finpartition (Finset.univ : Finset (SplitWord 1))) :
    IsTightSupport (cwSamePartitionQuotientSupport P) ↔
      ∃ kind : CWTightQuotientKind, P = kind.partition := by
  constructor
  · intro htight
    obtain ⟨lambda, mu, hP⟩ :=
      (cwSamePartitionQuotientSupport_isTight_iff_eq_linear P).mp htight
    obtain ⟨kind, hkind⟩ := cwLinearFinpartition_eq_kind lambda mu
    exact ⟨kind, hP.trans hkind⟩
  · rintro ⟨kind, rfl⟩
    apply (cwSamePartitionQuotientSupport_isTight_iff_eq_linear kind.partition).mpr
    exact ⟨kind.coefficients.1, kind.coefficients.2, rfl⟩

end AlgebraicComplexity.Examples
