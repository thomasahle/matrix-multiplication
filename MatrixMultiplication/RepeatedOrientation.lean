import AlgebraicComplexity.Probability.TensorialRelation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

/-!
# Repeated region orientations

This file formalizes the algebraic content of the repeated-region-orientation argument.  It
deliberately does not postulate a concrete model of tensors.  Instead, `DegenerationSystem`
records the properties of degeneration used by the argument, and the reusable
`AlgebraicComplexity.TensorialRelation` API handles labelled products and conjugated algorithms.

There are two layers.  The backwards-compatible theorem `arbitrary_orientations` tensors any
already-established family of one-region degenerations.  The stronger pipeline theorems derive
those oriented one-region degenerations by conjugating a fixed logical-coordinate algorithm.
They explicitly compose asymmetric hashing, `Y`-compatibility zeroing, `Z`-compatibility zeroing,
hole repair, and interface extraction, then assemble arbitrary labelled orientation lists and
arbitrary finite recursive sequences.  No theorem has an injectivity or distinctness hypothesis.
-/

open scoped BigOperators

namespace MatrixMultiplication

/-- The three tensor legs. -/
inductive Coord
  | X | Y | Z
  deriving DecidableEq, Repr

instance : Fintype Coord where
  elems := {Coord.X, Coord.Y, Coord.Z}
  complete x := by cases x <;> simp

/-- An orientation is a permutation of the three tensor legs. -/
abbrev Orientation := Equiv.Perm Coord

/-- The orientation `(X,Z,Y)` used for all six labels in the certificate. -/
def xzy : Orientation := Equiv.swap Coord.Y Coord.Z

/-- The identity orientation `(X,Y,Z)`. -/
def xyz : Orientation := Equiv.refl Coord

/-- The orientation `(Y,X,Z)`. -/
def yxz : Orientation := Equiv.swap Coord.X Coord.Y

/-- The orientation `(Y,Z,X)`. -/
def yzx : Orientation where
  toFun
    | Coord.X => Coord.Y
    | Coord.Y => Coord.Z
    | Coord.Z => Coord.X
  invFun
    | Coord.X => Coord.Z
    | Coord.Y => Coord.X
    | Coord.Z => Coord.Y
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

/-- The orientation `(Z,X,Y)`. -/
def zxy : Orientation where
  toFun
    | Coord.X => Coord.Z
    | Coord.Y => Coord.X
    | Coord.Z => Coord.Y
  invFun
    | Coord.X => Coord.Y
    | Coord.Y => Coord.Z
    | Coord.Z => Coord.X
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

/-- The orientation `(Z,Y,X)`. -/
def zyx : Orientation := Equiv.swap Coord.X Coord.Z

/-- The lexicographic six-slot orientation list used in the published theorem. -/
def publishedOrientation : Fin 6 → Orientation
  | 0 => xyz
  | 1 => xzy
  | 2 => yxz
  | 3 => yzx
  | 4 => zxy
  | 5 => zyx

/-- The published list contains every orientation exactly once. -/
theorem publishedOrientation_bijective : Function.Bijective publishedOrientation := by
  apply (Fintype.bijective_iff_injective_and_card publishedOrientation).2
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals
      exfalso
      revert h
      decide
  · decide

/-- The standard-slot bijection used by the one-hot reduction. -/
noncomputable def publishedOrientationEquiv : Fin 6 ≃ Orientation :=
  Equiv.ofBijective publishedOrientation publishedOrientation_bijective

@[simp] theorem xzy_X : xzy Coord.X = Coord.X := by
  decide

@[simp] theorem xzy_Y : xzy Coord.Y = Coord.Z := by
  decide

@[simp] theorem xzy_Z : xzy Coord.Z = Coord.Y := by
  decide

/-- An abstract tensor-degeneration calculus, with tensor product represented by multiplication. -/
class DegenerationSystem (Tensor : Type*) [CommMonoid Tensor] where
  Degenerates : Tensor → Tensor → Prop
  refl (T : Tensor) : Degenerates T T
  trans {T U V : Tensor} : Degenerates T U → Degenerates U V → Degenerates T V
  tensor {T₁ T₂ U₁ U₂ : Tensor} :
    Degenerates T₁ U₁ → Degenerates T₂ U₂ → Degenerates (T₁ * T₂) (U₁ * U₂)

namespace DegenerationSystem

variable {Tensor ι : Type*} [CommMonoid Tensor] [DegenerationSystem Tensor]

infix:50 " ⇝ " => DegenerationSystem.Degenerates

/-- View an abstract degeneration system as a reusable tensorial relation. -/
def tensorialRelation : AlgebraicComplexity.TensorialRelation Tensor where
  Rel := DegenerationSystem.Degenerates
  refl := DegenerationSystem.refl
  trans := DegenerationSystem.trans
  tensor := DegenerationSystem.tensor

/-- Tensoring finitely many independent degenerations gives a degeneration of their products. -/
theorem prod_degeneration [DecidableEq ι] (s : Finset ι) (input output : ι → Tensor)
    (h : ∀ i ∈ s, input i ⇝ output i) :
    (∏ i ∈ s, input i) ⇝ (∏ i ∈ s, output i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DegenerationSystem.refl (1 : Tensor)
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact DegenerationSystem.tensor (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/--
Repeated-orientation extension in its precise abstract form.

`orientation` is completely arbitrary.  Each labelled factor may therefore use the same
permutation, or any list with repetitions.  Distinctness cannot be used in the proof because it is
not present among the hypotheses.
-/
theorem arbitrary_orientations [Fintype ι] [DecidableEq ι]
    (orientation : ι → Orientation) (input : ι → Tensor)
    (oneRegionOutput : ι → Orientation → Tensor)
    (hOneRegion : ∀ r, input r ⇝ oneRegionOutput r (orientation r)) :
    (∏ r, input r) ⇝ (∏ r, oneRegionOutput r (orientation r)) := by
  apply prod_degeneration Finset.univ
  intro r _
  exact hOneRegion r

/-- The all-`(X,Z,Y)` six-region instance used by the numerical certificate. -/
theorem six_repeated_xzy
    (input : Fin 6 → Tensor) (oneRegionOutput : Fin 6 → Orientation → Tensor)
    (hOneRegion : ∀ r, input r ⇝ oneRegionOutput r xzy) :
    (∏ r, input r) ⇝ (∏ r, oneRegionOutput r xzy) := by
  exact arbitrary_orientations (fun _ : Fin 6 => xzy) input oneRegionOutput hOneRegion

/-! ## Reduction from the published distinct-slot theorem -/

/--
The actual repeated-orientation reduction.

`standardSlot : Fin 6 ≃ Orientation` is the published enumeration of the six distinct
permutations.  `hOneHot r s` is obtained by applying that published theorem to input factor `r`
with standard region `s` assigned weight one and its other five regions assigned weight zero.
For each desired labelled orientation, choose its unique standard slot and tensor the six
independent one-hot applications.

This proof does not assume that the hashing or constituent algorithm is orientation-equivariant,
and it remains valid even if distinctness is essential inside one invocation of the published
theorem: every one-hot invocation still uses its original six distinct slots.
-/
theorem arbitrary_orientation_list_of_standard_oneHot [Fintype ι]
    (standardSlot : Fin 6 ≃ Orientation)
    (input : ι → Tensor) (output : ι → Orientation → Tensor)
    (hOneHot : ∀ r s, input r ⇝ output r (standardSlot s))
    (orientation : ι → Orientation) :
    (∏ r, input r) ⇝ (∏ r, output r (orientation r)) := by
  exact (tensorialRelation (Tensor := Tensor)).arbitrary_labels_of_standard_oneHot
    standardSlot input output hOneHot orientation

/-- Six desired labelled regions may choose any orientation list, with repetitions, as a direct
corollary of the six-distinct-slot theorem's one-hot specializations. -/
theorem six_arbitrary_orientations_of_standard_oneHot
    (standardSlot : Fin 6 ≃ Orientation)
    (input : Fin 6 → Tensor) (output : Fin 6 → Orientation → Tensor)
    (hOneHot : ∀ r s, input r ⇝ output r (standardSlot s))
    (orientation : Fin 6 → Orientation) :
    (∏ r, input r) ⇝ (∏ r, output r (orientation r)) :=
  arbitrary_orientation_list_of_standard_oneHot
    standardSlot input output hOneHot orientation

/-- The certificate's all-`(X,Z,Y)` list follows from six independent one-hot applications of the
published distinct-slot theorem. -/
theorem six_repeated_xzy_of_standard_oneHot
    (standardSlot : Fin 6 ≃ Orientation)
    (input : Fin 6 → Tensor) (output : Fin 6 → Orientation → Tensor)
    (hOneHot : ∀ r s, input r ⇝ output r (standardSlot s)) :
    (∏ r, input r) ⇝ (∏ r, output r xzy) :=
  six_arbitrary_orientations_of_standard_oneHot
    standardSlot input output hOneHot (fun _ ↦ xzy)

/-- Repeated orientations derived directly from the published theorem quantified over all legal
six-slot weight vectors.  The one-hot instances are constructed internally as point masses, so
they are no longer hypotheses of this theorem. -/
theorem arbitrary_orientation_list_of_standard_weights [Fintype ι]
    (standardSlot : Fin 6 ≃ Orientation)
    (input : ι → Tensor)
    (standardOutput : ι → AlgebraicComplexity.ProbabilityVector (Fin 6) → Tensor)
    (output : ι → Orientation → Tensor)
    (hStandard : ∀ r weights, input r ⇝ standardOutput r weights)
    (hPointMassOutput : ∀ r s,
      standardOutput r (AlgebraicComplexity.ProbabilityVector.pointMass s) =
        output r (standardSlot s))
    (orientation : ι → Orientation) :
    (∏ r, input r) ⇝ (∏ r, output r (orientation r)) := by
  exact (tensorialRelation (Tensor := Tensor)).arbitrary_labels_of_standard_weights
    standardSlot input standardOutput output hStandard hPointMassOutput orientation

/-- All six labels may use `(X,Z,Y)`, derived only from the original theorem for normalized
standard-slot weights and the calculation of its point-mass output. -/
theorem six_repeated_xzy_of_standard_weights
    (standardSlot : Fin 6 ≃ Orientation)
    (input : Fin 6 → Tensor)
    (standardOutput : Fin 6 → AlgebraicComplexity.ProbabilityVector (Fin 6) → Tensor)
    (output : Fin 6 → Orientation → Tensor)
    (hStandard : ∀ r weights, input r ⇝ standardOutput r weights)
    (hPointMassOutput : ∀ r s,
      standardOutput r (AlgebraicComplexity.ProbabilityVector.pointMass s) =
        output r (standardSlot s)) :
    (∏ r, input r) ⇝ (∏ r, output r xzy) :=
  arbitrary_orientation_list_of_standard_weights standardSlot input standardOutput output
    hStandard hPointMassOutput (fun _ ↦ xzy)

/-- The preceding theorem with the concrete published lexicographic orientation enumeration. -/
theorem six_repeated_xzy_of_published_weights
    (input : Fin 6 → Tensor)
    (standardOutput : Fin 6 → AlgebraicComplexity.ProbabilityVector (Fin 6) → Tensor)
    (output : Fin 6 → Orientation → Tensor)
    (hStandard : ∀ r weights, input r ⇝ standardOutput r weights)
    (hPointMassOutput : ∀ r s,
      standardOutput r (AlgebraicComplexity.ProbabilityVector.pointMass s) =
        output r (publishedOrientation s)) :
    (∏ r, input r) ⇝ (∏ r, output r xzy) :=
  six_repeated_xzy_of_standard_weights publishedOrientationEquiv input standardOutput output
    hStandard hPointMassOutput

/-! ## Orientation-parametric one-region pipelines -/

/-- Coordinate relabelling preserves degeneration.  This is the sole equivariance hypothesis
needed to conjugate the one-region algorithm. -/
def OrientationEquivariant [MulAction Orientation Tensor] : Prop :=
  (tensorialRelation (Tensor := Tensor)).IsEquivariant Orientation

/-- A named factorization of the one-region algorithm into the five operations relevant to the
distinctness audit.  Every field carries its own degeneration proof. -/
structure RegionPipeline (Tensor : Type*) [CommMonoid Tensor] [DegenerationSystem Tensor] where
  asymmetricHashing : AlgebraicComplexity.TensorialRelation.Stage
    (tensorialRelation (Tensor := Tensor))
  yCompatibilityZeroing : AlgebraicComplexity.TensorialRelation.Stage
    (tensorialRelation (Tensor := Tensor))
  zCompatibilityZeroing : AlgebraicComplexity.TensorialRelation.Stage
    (tensorialRelation (Tensor := Tensor))
  holeRepair : AlgebraicComplexity.TensorialRelation.Stage
    (tensorialRelation (Tensor := Tensor))
  interfaceExtraction : AlgebraicComplexity.TensorialRelation.Stage
    (tensorialRelation (Tensor := Tensor))

namespace RegionPipeline

/-- The complete one-region algorithm, in paper order. -/
def stage (pipeline : RegionPipeline Tensor) :
    AlgebraicComplexity.TensorialRelation.Stage (tensorialRelation (Tensor := Tensor)) :=
  AlgebraicComplexity.TensorialRelation.Stage.sequence
    [pipeline.asymmetricHashing, pipeline.yCompatibilityZeroing,
      pipeline.zCompatibilityZeroing, pipeline.holeRepair, pipeline.interfaceExtraction]

/-- Every named one-region pipeline is a valid degeneration. -/
theorem valid (pipeline : RegionPipeline Tensor) (T : Tensor) :
    T ⇝ pipeline.stage.run T :=
  pipeline.stage.valid T

/-- Conjugating the whole one-region pipeline by any coordinate permutation is valid.  This
derives orientation-parametricity from relabelling equivariance rather than assuming one theorem
for each of the six orientations. -/
theorem any_orientation [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (pipeline : RegionPipeline Tensor) (orientation : Orientation) (T : Tensor) :
    T ⇝ ((pipeline.stage).conjugate hEquivariant orientation).run T :=
  ((pipeline.stage).conjugate hEquivariant orientation).valid T

end RegionPipeline

/-- A division of one tensor into independently labelled region factors. -/
abbrev RegionDivision (Tensor : Type*) [CommMonoid Tensor] [DegenerationSystem Tensor]
    (ι : Type*) [Fintype ι] :=
  AlgebraicComplexity.TensorialRelation.LabelledDecomposition
    (tensorialRelation (Tensor := Tensor)) ι

/-- Constituent-stage time sharing.  First perform the orientation-free labelled division of the
input interface tensor.  On each factor, invoke the published six-distinct-orientation theorem
with exactly one standard slot active.  The desired slot may be chosen independently for every
label, so repetitions are allowed. -/
theorem constituent_arbitrary_orientation_list_of_standard_oneHot [Fintype ι]
    (standardSlot : Fin 6 ≃ Orientation)
    (division : RegionDivision Tensor ι) (output : ι → Orientation → Tensor)
    (orientation : ι → Orientation) (T : Tensor)
    (hOneHot : ∀ r s,
      division.factor T r ⇝ output r (standardSlot s)) :
    T ⇝ ∏ r, output r (orientation r) := by
  exact
    AlgebraicComplexity.TensorialRelation.LabelledDecomposition.arbitrary_labels_of_standard_oneHot
      (tensorialRelation (Tensor := Tensor)) division standardSlot output orientation T hOneHot

/-- Six-label constituent theorem obtained from standard one-hot invocations. -/
theorem constituent_six_arbitrary_orientations_of_standard_oneHot
    (standardSlot : Fin 6 ≃ Orientation)
    (division : RegionDivision Tensor (Fin 6))
    (output : Fin 6 → Orientation → Tensor)
    (orientation : Fin 6 → Orientation) (T : Tensor)
    (hOneHot : ∀ r s,
      division.factor T r ⇝ output r (standardSlot s)) :
    T ⇝ ∏ r, output r (orientation r) :=
  constituent_arbitrary_orientation_list_of_standard_oneHot
    standardSlot division output orientation T hOneHot

/-- All six recursive constituent labels may select `(X,Z,Y)`. -/
theorem constituent_six_repeated_xzy_of_standard_oneHot
    (standardSlot : Fin 6 ≃ Orientation)
    (division : RegionDivision Tensor (Fin 6))
    (output : Fin 6 → Orientation → Tensor) (T : Tensor)
    (hOneHot : ∀ r s,
      division.factor T r ⇝ output r (standardSlot s)) :
    T ⇝ ∏ r, output r xzy :=
  constituent_six_arbitrary_orientations_of_standard_oneHot
    standardSlot division output (fun _ ↦ xzy) T hOneHot

/-- Constituent-stage reduction derived from a standard theorem whose legal parameters are one
normalized six-slot weight vector for every interface term.  All terms in an outer label select
the same point mass; consequently they remain grouped before the branch minimum is taken. -/
theorem constituent_arbitrary_orientation_list_of_standard_termWeights
    [Fintype ι] {Term : Type*}
    (standardSlot : Fin 6 ≃ Orientation)
    (division : RegionDivision Tensor ι)
    (standardOutput : Tensor → ι →
      (Term → AlgebraicComplexity.ProbabilityVector (Fin 6)) → Tensor)
    (output : Tensor → ι → Orientation → Tensor)
    (orientation : ι → Orientation) (T : Tensor)
    (hStandard : ∀ r weights,
      division.factor T r ⇝ standardOutput T r weights)
    (hPointMassOutput : ∀ r s,
      standardOutput T r
          (AlgebraicComplexity.ProbabilityVector.constantPointMass (κ := Term) s) =
        output T r (standardSlot s)) :
    T ⇝ ∏ r, output T r (orientation r) := by
  exact
    AlgebraicComplexity.TensorialRelation.LabelledDecomposition.arbitrary_labels_of_standard_parameters
      (tensorialRelation (Tensor := Tensor)) division standardSlot
      (AlgebraicComplexity.ProbabilityVector.constantPointMass (κ := Term))
      standardOutput output orientation T hStandard hPointMassOutput

/-- Six constituent labels all selecting `(X,Z,Y)`, obtained from the published theorem over
term-indexed legal weight vectors rather than from separately assumed one-hot cases. -/
theorem constituent_six_repeated_xzy_of_standard_termWeights
    {Term : Type*} (standardSlot : Fin 6 ≃ Orientation)
    (division : RegionDivision Tensor (Fin 6))
    (standardOutput : Tensor → Fin 6 →
      (Term → AlgebraicComplexity.ProbabilityVector (Fin 6)) → Tensor)
    (output : Tensor → Fin 6 → Orientation → Tensor) (T : Tensor)
    (hStandard : ∀ r weights,
      division.factor T r ⇝ standardOutput T r weights)
    (hPointMassOutput : ∀ r s,
      standardOutput T r
          (AlgebraicComplexity.ProbabilityVector.constantPointMass (κ := Term) s) =
        output T r (standardSlot s)) :
    T ⇝ ∏ r, output T r xzy :=
  constituent_arbitrary_orientation_list_of_standard_termWeights
    standardSlot division standardOutput output (fun _ ↦ xzy) T
    hStandard hPointMassOutput

/-- Concrete published-slot version of the all-`(X,Z,Y)` constituent reduction. -/
theorem constituent_six_repeated_xzy_of_published_termWeights
    {Term : Type*} (division : RegionDivision Tensor (Fin 6))
    (standardOutput : Tensor → Fin 6 →
      (Term → AlgebraicComplexity.ProbabilityVector (Fin 6)) → Tensor)
    (output : Tensor → Fin 6 → Orientation → Tensor) (T : Tensor)
    (hStandard : ∀ r weights,
      division.factor T r ⇝ standardOutput T r weights)
    (hPointMassOutput : ∀ r s,
      standardOutput T r
          (AlgebraicComplexity.ProbabilityVector.constantPointMass (κ := Term) s) =
        output T r (publishedOrientation s)) :
    T ⇝ ∏ r, output T r xzy :=
  constituent_six_repeated_xzy_of_standard_termWeights publishedOrientationEquiv
    division standardOutput output T hStandard hPointMassOutput

/-- A recursive constituent level justified only by one-hot specializations of the published
six-distinct-slot theorem. -/
abbrev StandardConstituentLevel
    (Tensor : Type*) [CommMonoid Tensor] [DegenerationSystem Tensor]
    (standardSlot : Fin 6 ≃ Orientation) :=
  AlgebraicComplexity.TensorialRelation.StandardSlotLevel
    (tensorialRelation (Tensor := Tensor)) (Fin 6) (Fin 6) Orientation standardSlot

/-- Recursively compose any finite list of one-hot-derived constituent levels. -/
noncomputable def recursiveStandardConstituentPipeline
    (standardSlot : Fin 6 ≃ Orientation)
    (levels : List (StandardConstituentLevel Tensor standardSlot)) :
    AlgebraicComplexity.TensorialRelation.Stage (tensorialRelation (Tensor := Tensor)) :=
  AlgebraicComplexity.TensorialRelation.StandardSlotLevel.recursive levels

/-- Every finite recursive tower obtained by the one-hot reduction is a valid degeneration. -/
theorem recursive_constituent_of_standard_oneHot
    (standardSlot : Fin 6 ≃ Orientation)
    (levels : List (StandardConstituentLevel Tensor standardSlot)) (T : Tensor) :
    T ⇝ (recursiveStandardConstituentPipeline standardSlot levels).run T :=
  AlgebraicComplexity.TensorialRelation.StandardSlotLevel.recursive_valid levels T

/-- Global-stage theorem for an arbitrary finite labelled orientation assignment.  In
particular, `orientation` need not be injective or surjective. -/
theorem global_arbitrary_orientation_list [Fintype ι] [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor ι) (orientation : ι → Orientation)
    (pipeline : ι → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ (division.assemble hEquivariant orientation (fun r ↦ (pipeline r).stage)).run T :=
  (division.assemble hEquivariant orientation (fun r ↦ (pipeline r).stage)).valid T

/-- Unfolded form of `global_arbitrary_orientation_list`.  It displays the conjugation applied to
each labelled factor and makes the complete absence of cross-region orientation conditions
syntactically explicit. -/
theorem global_arbitrary_orientation_list_explicit
    [Fintype ι] [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor ι) (orientation : ι → Orientation)
    (pipeline : ι → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ ∏ r, (orientation r)⁻¹ •
      (pipeline r).stage.run (orientation r • division.factor T r) := by
  change T ⇝
    (division.assemble hEquivariant orientation (fun r ↦ (pipeline r).stage)).run T
  exact global_arbitrary_orientation_list hEquivariant division orientation pipeline T

/-- The global theorem specialized to six labels, still with no distinctness hypothesis. -/
theorem global_six_arbitrary_orientation_list [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor (Fin 6)) (orientation : Fin 6 → Orientation)
    (pipeline : Fin 6 → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ (division.assemble hEquivariant orientation (fun r ↦ (pipeline r).stage)).run T :=
  global_arbitrary_orientation_list hEquivariant division orientation pipeline T

/-- Unfolded six-label global theorem.  `orientation : Fin 6 → Orientation` is an arbitrary list,
not an enumeration of the permutation group. -/
theorem global_six_arbitrary_orientation_list_explicit [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor (Fin 6)) (orientation : Fin 6 → Orientation)
    (pipeline : Fin 6 → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ ∏ r, (orientation r)⁻¹ •
      (pipeline r).stage.run (orientation r • division.factor T r) :=
  global_arbitrary_orientation_list_explicit hEquivariant division orientation pipeline T

/-- Six independent labelled strategies may all use `(X,Z,Y)`. -/
theorem global_six_repeated_xzy_pipeline [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor (Fin 6))
    (pipeline : Fin 6 → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ (division.assemble hEquivariant (fun _ : Fin 6 ↦ xzy)
      (fun r ↦ (pipeline r).stage)).run T :=
  global_six_arbitrary_orientation_list hEquivariant division
    (fun _ : Fin 6 ↦ xzy) pipeline T

/-- The same all-`(X,Z,Y)` conclusion with the conjugations exposed. -/
theorem global_six_repeated_xzy_pipeline_explicit [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor (Fin 6))
    (pipeline : Fin 6 → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ ∏ r, xzy⁻¹ • (pipeline r).stage.run (xzy • division.factor T r) :=
  global_six_arbitrary_orientation_list_explicit hEquivariant division
    (fun _ : Fin 6 ↦ xzy) pipeline T

/-- The recursive constituent theorem has the same six-labelled assembly shape as the global
theorem.  This named version records the one-level statement used at every recursive depth. -/
theorem constituent_six_arbitrary_orientation_list_explicit
    [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor (Fin 6)) (orientation : Fin 6 → Orientation)
    (pipeline : Fin 6 → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ ∏ r, (orientation r)⁻¹ •
      (pipeline r).stage.run (orientation r • division.factor T r) :=
  global_six_arbitrary_orientation_list_explicit hEquivariant division orientation pipeline T

/-- One recursive constituent level may use `(X,Z,Y)` on all six independently parametrized
labels. -/
theorem constituent_six_repeated_xzy_pipeline_explicit
    [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (division : RegionDivision Tensor (Fin 6))
    (pipeline : Fin 6 → RegionPipeline Tensor) (T : Tensor) :
    T ⇝ ∏ r, xzy⁻¹ • (pipeline r).stage.run (xzy • division.factor T r) :=
  constituent_six_arbitrary_orientation_list_explicit hEquivariant division
    (fun _ : Fin 6 ↦ xzy) pipeline T

/-- One recursive constituent level.  Its six (or more generally `ι`) labelled regions have
independent pipelines and an arbitrary orientation function. -/
structure ConstituentLevel (Tensor : Type*) [CommMonoid Tensor] [DegenerationSystem Tensor]
    (ι : Type*) [Fintype ι] where
  division : RegionDivision Tensor ι
  orientation : ι → Orientation
  pipeline : ι → RegionPipeline Tensor

namespace ConstituentLevel

/-- Assemble one recursive constituent level into a single valid stage. -/
noncomputable def stage [Fintype ι] [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (level : ConstituentLevel Tensor ι) :
    AlgebraicComplexity.TensorialRelation.Stage (tensorialRelation (Tensor := Tensor)) :=
  level.division.assemble hEquivariant level.orientation
    (fun r ↦ (level.pipeline r).stage)

/-- A constituent level is valid for its arbitrary, possibly repeated orientation list. -/
theorem valid [Fintype ι] [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (level : ConstituentLevel Tensor ι) (T : Tensor) :
    T ⇝ (level.stage hEquivariant).run T :=
  (level.stage hEquivariant).valid T

end ConstituentLevel

/-- Compose an arbitrary finite recursive tower of constituent levels.  Each level may choose a
different arbitrary orientation list, including repetitions. -/
noncomputable def recursiveConstituentPipeline [Fintype ι] [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (levels : List (ConstituentLevel Tensor ι)) :
    AlgebraicComplexity.TensorialRelation.Stage (tensorialRelation (Tensor := Tensor)) :=
  AlgebraicComplexity.TensorialRelation.Stage.sequence
    (levels.map fun level ↦ level.stage hEquivariant)

/-- Recursive constituent theorem with arbitrary orientation lists and no distinctness
assumption at any level. -/
theorem recursive_constituent_arbitrary_orientation_lists
    [Fintype ι] [MulAction Orientation Tensor]
    (hEquivariant : OrientationEquivariant (Tensor := Tensor))
    (levels : List (ConstituentLevel Tensor ι)) (T : Tensor) :
    T ⇝ (recursiveConstituentPipeline hEquivariant levels).run T :=
  (recursiveConstituentPipeline hEquivariant levels).valid T

end DegenerationSystem

/-- Numerical data that add when independent labelled regions are tensored. -/
structure RegionOutput where
  copies : ℕ
  retainedExponent : ℝ
  logDimension : Coord → ℝ

/-- Assembly of independently processed labelled regions. -/
noncomputable def assembleRegions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (out : ι → RegionOutput) :
    RegionOutput where
  copies := ∏ r, (out r).copies
  retainedExponent := ∑ r, (out r).retainedExponent
  logDimension W := ∑ r, (out r).logDimension W

@[simp] theorem assembleRegions_copies {ι : Type*} [Fintype ι] [DecidableEq ι]
    (out : ι → RegionOutput) :
    (assembleRegions out).copies = ∏ r, (out r).copies := rfl

@[simp] theorem assembleRegions_retainedExponent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (out : ι → RegionOutput) :
    (assembleRegions out).retainedExponent = ∑ r, (out r).retainedExponent := rfl

@[simp] theorem assembleRegions_logDimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (out : ι → RegionOutput) (W : Coord) :
    (assembleRegions out).logDimension W = ∑ r, (out r).logDimension W := rfl

/-- Distributivity for two direct sums, the finite algebra behind Lemma 3.2. -/
theorem tensor_two_directSums {A I J : Type*} [CommSemiring A] [Fintype I] [Fintype J]
    (left : I → A) (right : J → A) :
    (∑ i, left i) * (∑ j, right j) = ∑ i, ∑ j, left i * right j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- A labelled mixture; orientations do not occur in its definition. -/
noncomputable def labelledMixture {R A : Type*} [Fintype R]
    (weight : R → ℝ) (value : R → A → ℝ) (a : A) : ℝ :=
  ∑ r, weight r * value r a

/-- The same mixture with an explicit, deliberately unused orientation assignment. -/
noncomputable def orientationCovariantMixture {R A : Type*} [Fintype R]
    (_orientation : R → Orientation) (weight : R → ℝ)
    (value : R → A → ℝ) : A → ℝ :=
  labelledMixture weight value

/-- Complete-split mixture identities are unchanged when orientation labels are replaced. -/
theorem labelledMixture_orientation_irrelevant {R A : Type*} [Fintype R]
    (weight : R → ℝ) (value : R → A → ℝ)
    (orientation₁ orientation₂ : R → Orientation) :
    orientationCovariantMixture orientation₁ weight value =
      orientationCovariantMixture orientation₂ weight value := rfl

end MatrixMultiplication
