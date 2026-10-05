/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite
import AlgebraicComplexity.Tensor.Relation

set_option autoImplicit false

/-!
# Probability-vector adapters for tensorial relations

The paper-independent relation calculus accepts an arbitrary admissible parameter type and an
arbitrary one-hot map.  This module specializes that interface to `ProbabilityVector`, whose
point masses supply the one-hot parameters used by repeated-orientation arguments.

Keeping these three wrappers here prevents the reusable `AlgebraicComplexity.Tensor` umbrella
from depending on probability.  Their fully qualified declaration names are unchanged from the
original combined implementation, so downstream theorem statements need no migration.

The repeated-orientation clients model the region relabelings used in:

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace TensorialRelation

variable {A : Type u} [CommMonoid A]

/-- **A standard theorem for all probability weights supplies arbitrary symmetry labels.**
Point masses are legal normalized weights, so each requested label is obtained by specializing
the standard theorem at the corresponding point mass.

Proof sketch: instantiate `arbitrary_labels_of_standard_parameters` with
`ProbabilityVector.pointMass`. -/
theorem arbitrary_labels_of_standard_weights
    {Slot Symmetry : Type*} {ι : Type v} [Fintype ι]
    [Fintype Slot] [DecidableEq Slot]
    (D : TensorialRelation A) (standardSlot : Slot ≃ Symmetry)
    (input : ι → A) (standardOutput : ι → ProbabilityVector Slot → A)
    (output : ι → Symmetry → A)
    (hStandard : ∀ r weights, D.Rel (input r) (standardOutput r weights))
    (hPointMassOutput : ∀ r s,
      standardOutput r (ProbabilityVector.pointMass s) = output r (standardSlot s))
    (orientation : ι → Symmetry) :
    D.Rel (∏ r, input r) (∏ r, output r (orientation r)) :=
  D.arbitrary_labels_of_standard_parameters standardSlot ProbabilityVector.pointMass
    input standardOutput output hStandard hPointMassOutput orientation

/-- **Probability-weight specialization after a labelled decomposition.**
First divide the source into its labelled factors, then specialize the standard theorem at the
point mass selecting each requested orientation.

Proof sketch: apply the parameter-generic labelled theorem with
`ProbabilityVector.pointMass`. -/
theorem LabelledDecomposition.arbitrary_labels_of_standard_weights
    {Slot Symmetry : Type*} {ι : Type v} [Fintype ι]
    [Fintype Slot] [DecidableEq Slot]
    (D : TensorialRelation A) (division : LabelledDecomposition D ι)
    (standardSlot : Slot ≃ Symmetry)
    (standardOutput : A → ι → ProbabilityVector Slot → A)
    (output : A → ι → Symmetry → A) (orientation : ι → Symmetry) (T : A)
    (hStandard : ∀ r weights,
      D.Rel (division.factor T r) (standardOutput T r weights))
    (hPointMassOutput : ∀ r s,
      standardOutput T r (ProbabilityVector.pointMass s) =
        output T r (standardSlot s)) :
    D.Rel T (∏ r, output T r (orientation r)) :=
  LabelledDecomposition.arbitrary_labels_of_standard_parameters D division standardSlot
    ProbabilityVector.pointMass standardOutput output orientation T hStandard hPointMassOutput

/-- **Build a recursive standard-slot level from a theorem quantified over probability
weights.**  Point-mass specialization discharges the generic constructor's one-hot premise.

Proof sketch: instantiate `StandardSlotLevel.ofStandardParameters` with point masses. -/
def StandardSlotLevel.ofStandardWeights
    {ι : Type v} [Fintype ι] {Slot Symmetry : Type*}
    [Fintype Slot] [DecidableEq Slot] {standardSlot : Slot ≃ Symmetry}
    (D : TensorialRelation A) (division : LabelledDecomposition D ι)
    (orientation : ι → Symmetry)
    (standardOutput : A → ι → ProbabilityVector Slot → A)
    (output : A → ι → Symmetry → A)
    (hStandard : ∀ T r weights,
      D.Rel (division.factor T r) (standardOutput T r weights))
    (hPointMassOutput : ∀ T r s,
      standardOutput T r (ProbabilityVector.pointMass s) =
        output T r (standardSlot s)) :
    StandardSlotLevel D ι Slot Symmetry standardSlot :=
  StandardSlotLevel.ofStandardParameters D division orientation ProbabilityVector.pointMass
    standardOutput output hStandard hPointMassOutput

end TensorialRelation

end AlgebraicComplexity
