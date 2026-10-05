/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ModeledMarkedHashingProductModel

set_option autoImplicit false

/-!
# Support of a product partition model

The product of native partition models represents exactly the Cartesian product of the target
families represented by its factors.  This module records that identity at the level of native
block addresses: aggregate modeled targets are the factorwise modeled targets, with the factor
and tensor-leg arguments transposed.

Keeping this elementary support law separate from tensor products lets clients combine it with
whichever partitioned-tensor assembly matches their source.  In particular, no restriction,
degeneration, or hashing theorem is assumed here.  The result is the generic finite-set
bookkeeping used by the aggregate constituent construction of [alman2025more, Sections 6--7].

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity

universe u v w

namespace ProgressionHash.LegalTriple.PartitionModel

variable {R : Type u} [Field R]
variable {target : R}

noncomputable section

/-- Aggregate modeled targets are precisely tuples of factorwise modeled targets.

The right-hand side first chooses one native three-leg address in every factor and then
transposes the factor and leg arguments.  No inclusion `present e ⊆ ambient e` is needed: this is
an identity between the two finite image constructions and does not use the model's encoding
law.

Proof sketch: expand membership in the two images.  An aggregate legal triple has a unique tuple
of factor triples; `aggregateFactor_aggregate` says that the product model recovers those factors.
Conversely, choose a legal triple representing each factor address and aggregate those choices. -/
theorem modeledTargets_aggregateModel
    {E : Type v} [Fintype E] [DecidableEq E]
    {ι : E → Type w} [∀ e, Fintype (ι e)]
    {A : E → Tensor.Leg → Type w}
    (ambient present : ∀ e, Finset (LegalTriple R (ι e) target))
    (models : ∀ e, PartitionModel
      (R := R) (ι := ι e) (target := target) (A := A e) (ambient e)) :
    (aggregateModel ambient models).modeledTargets (aggregateTargets present) =
      (Fintype.piFinset fun e ↦ (models e).modeledTargets (present e)).map
        { toFun := fun blocks c e ↦ blocks e c
          inj' := by
            intro left right h
            funext e c
            exact congrFun (congrFun h c) e } := by
  classical
  ext blocks
  constructor
  · intro hblocks
    have hexists : ∃ triple,
        triple ∈ aggregateTargets present ∧
          (aggregateModel ambient models).address triple = blocks := by
      simpa only [modeledTargets, Finset.mem_image] using hblocks
    obtain ⟨triple, htriple, rfl⟩ := hexists
    obtain ⟨factors, hfactors, rfl⟩ :=
      (mem_aggregateTargets present triple).mp htriple
    refine Finset.mem_map.mpr ⟨fun e c ↦ (models e).address (factors e) c, ?_, ?_⟩
    · simp only [Fintype.mem_piFinset]
      intro e
      unfold modeledTargets
      exact Finset.mem_image.mpr ⟨factors e, hfactors e, rfl⟩
    · funext c e
      change (models e).address (factors e) c =
        (models e).address (aggregateFactor (aggregate factors) e) c
      rw [aggregateFactor_aggregate]
  · intro hblocks
    obtain ⟨factorBlocks, hfactorBlocks, rfl⟩ := Finset.mem_map.mp hblocks
    have hfactorBlocks' :
        ∀ e, factorBlocks e ∈ (models e).modeledTargets (present e) := by
      simpa only [Fintype.mem_piFinset] using hfactorBlocks
    have hexists : ∀ e, ∃ triple,
        triple ∈ present e ∧ (models e).address triple = factorBlocks e := by
      intro e
      simpa only [modeledTargets, Finset.mem_image] using hfactorBlocks' e
    choose factors hfactors haddresses using hexists
    have haggregate : ∃ triple,
        triple ∈ aggregateTargets present ∧
          (aggregateModel ambient models).address triple =
            (fun c e ↦ factorBlocks e c) := by
      refine ⟨aggregate factors, ?_, ?_⟩
      · exact (mem_aggregateTargets present (aggregate factors)).mpr
          ⟨factors, hfactors, rfl⟩
      · funext c e
        change (models e).address (aggregateFactor (aggregate factors) e) c =
          factorBlocks e c
        rw [aggregateFactor_aggregate]
        exact congrFun (haddresses e) c
    change (fun c e ↦ factorBlocks e c) ∈
      (aggregateModel ambient models).modeledTargets (aggregateTargets present)
    simpa only [modeledTargets, Finset.mem_image] using haggregate

end

end ProgressionHash.LegalTriple.PartitionModel

end AlgebraicComplexity
