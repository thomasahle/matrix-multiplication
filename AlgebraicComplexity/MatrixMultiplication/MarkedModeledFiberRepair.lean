/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.GroupedVariableHoleRepair
import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing

set_option autoImplicit false

/-!
# Repair after marked partitioned-power isolation

Marked affine hashing first separates actual constituents of a partitioned tensor power.  Those
constituents need not be intact copies of the desired child: each may only restrict to a differently
damaged box in one common target partition.  This module composes that honest pointwise
normalization with the generic seven-branch hole-repair theorem.

The result is deliberately relation-parametric at the semantic boundary.  In particular, it does
not replace an actual constituent by an ideal positive-power constituent through an equality
hypothesis.  A paper client must construct the `ModeledFiberFamily` from its literal deleted
variables and prove the sparse-copy count.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*; the damaged-copy and
  repair step is `papers/sources/2404.16349/constituent.tex:338-348,473-497`.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*; the mixed
  cyclic assembly explicitly leaves both local input-profile and repair conditions to its clients,
  `better_bound/paper.tex:2034-2036`.  Applying one marked hash before this adapter is new
  Total-Weight plumbing, not a theorem attributed to [alman2025more].
-/

namespace AlgebraicComplexity.Tensor.Restricts

universe u r

variable {K : Type u} [CommSemiring K]
variable {R : Type r} [Field R]
variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {support : Finset (BlockAddress A)}
variable {n : ℕ}
variable {V : ∀ c, PositiveWord (A c) n → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **Marked isolated constituents that model enough sparse damaged boxes restrict to intact
copies.**

The marked words are isolated against the full ambient word family.  Each resulting actual
constituent is then allowed its own restriction to a tensor in the common-space family `family`.
The `ModeledFiberFamily` identifies those tensors with damaged boxes of `P`; the final numerical
hypothesis supplies one complete repair tree for each requested output.

Proof sketch: apply marked legwise isolation to obtain the indexed direct sum of actual
constituents.  Apply `hconstituent` independently to every summand.  The generic sparse-family
theorem repairs that intermediate indexed sum to intact boxes, and transitivity composes the three
restrictions. -/
theorem modeledTargets_to_repairedMarkedLegwiseIsolatedIndexedDirectSum
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hmarked : markedWords ⊆ ambientWords)
    (buckets : Finset R) (hBuckets : ThreeAPFree (buckets : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (Q : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : Q.support = H.modeledAddresses n (H.legalTargets n ambientWords))
    {U : Leg → Type u}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (family : H.markedLegwiseIsolatedPowerAddresses
      n ambientWords markedWords buckets seed → Tensor3 K U)
    (hconstituent : ∀ selected,
      Restricts (Q.constituent selected.1) (family selected))
    {D : Leg → Type u} [∀ c, Fintype (D c)] [∀ c, DecidableEq (D c)]
    {W : ∀ c, D c → Type u}
    [∀ c d, AddCommMonoid (W c d)] [∀ c d, Module K (W c d)]
    (P : PartitionedTensor (K := K) (A := D) W)
    (model : HoleRepair.ModeledFiberFamily P family)
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : HoleRepair.UniformStructureRelabelings (G := Relabel) P)
    {Output : Type u} [Fintype Output] [DecidableEq Output]
    {base : ℕ} (hbase : 1 < base) (depth : ℕ)
    (target : ∀ c, Finset (D c))
    (hdepth : HoleRepair.logarithmicRepairDepth base target ≤ depth)
    (hcount : Fintype.card Output * HoleRepair.sevenBranchBudget depth ≤
      (model.sparseIndices base).card) :
    Restricts Q.realize
      (Tensor.indexedDirectSum
        (fun _output : Output ↦ (P.box target).realize)) := by
  classical
  let Selected := H.markedLegwiseIsolatedPowerAddresses
    n ambientWords markedWords buckets seed
  have hisolated : Restricts Q.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := V) Selected)
        (fun selected : Selected ↦ Q.constituent selected.1)) := by
    exact modeledTargets_to_markedLegwiseIsolatedIndexedDirectSum
      H ambientWords markedWords hmarked buckets hBuckets seed Q hsupport
  have hretyped : Restricts
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := V) Selected)
        (fun selected : Selected ↦ Q.constituent selected.1))
      (Tensor.indexedDirectSum family) := by
    exact indexedDirectSum hconstituent
  obtain ⟨_plans, _pick, _holes, hrepair⟩ :=
    model.exists_repairPlans_of_mul_budget_le_sparse
      relabelings hbase depth target hdepth hcount
  exact hisolated.trans (hretyped.trans hrepair)

end AlgebraicComplexity.Tensor.Restricts
