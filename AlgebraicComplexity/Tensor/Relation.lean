/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Basic

/-!
# Tensorial relations and equivariant algorithms

This file isolates a small calculus shared by restriction, degeneration, and zeroing arguments.
The elements of `A` represent tensors, multiplication represents tensor product, and a
`TensorialRelation A` is a reflexive, transitive relation closed under tensor product.

The main applications are labelled time sharing and coordinate-asymmetric algorithms.  The
one-hot API derives arbitrary repeated symmetry labels from a theorem with a fixed standard slot
for every symmetry.  A separate conjugation API handles genuinely equivariant stages.  In both
cases the orientation assignment is an arbitrary function: no injectivity, surjectivity, or
distinctness hypothesis occurs anywhere in the API.

The definitions are deliberately independent of three-legged tensors and of polynomial
degeneration.  They can also be instantiated by exact restriction, monomial degeneration,
border-degeneration certificates, or other tensor-product-compatible relations.

Specializations to `ProbabilityVector` point masses live in
`AlgebraicComplexity.Probability.TensorialRelation`; keeping them outside this file preserves the
probability-free public tensor boundary.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

/-- A reflexive and transitive tensor transformation closed under tensor products. -/
structure TensorialRelation (A : Type u) [CommMonoid A] where
  Rel : A → A → Prop
  refl (T : A) : Rel T T
  trans {T S U : A} : Rel T S → Rel S U → Rel T U
  tensor {T₁ T₂ S₁ S₂ : A} : Rel T₁ S₁ → Rel T₂ S₂ → Rel (T₁ * T₂) (S₁ * S₂)

namespace TensorialRelation

variable {A : Type u} [CommMonoid A]

/-- Tensor finitely many transformations indexed by a finset. -/
theorem finset_prod {ι : Type v} [DecidableEq ι] (D : TensorialRelation A)
    (s : Finset ι) (input output : ι → A)
    (h : ∀ i ∈ s, D.Rel (input i) (output i)) :
    D.Rel (∏ i ∈ s, input i) (∏ i ∈ s, output i) := by
  induction s using Finset.induction_on with
  | empty => simpa using D.refl (1 : A)
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact D.tensor (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Tensor a finite labelled family of transformations. -/
theorem fintype_prod {ι : Type v} [Fintype ι] (D : TensorialRelation A)
    (input output : ι → A) (h : ∀ i, D.Rel (input i) (output i)) :
    D.Rel (∏ i, input i) (∏ i, output i) := by
  classical
  exact D.finset_prod Finset.univ input output (fun i _ ↦ h i)

/-- A group action preserves a tensorial relation. -/
def IsEquivariant (D : TensorialRelation A) (G : Type*) [Group G] [MulAction G A] : Prop :=
  ∀ (g : G) {T S : A}, D.Rel T S → D.Rel (g • T) (g • S)

/-- A uniformly valid tensor transformation.  It may represent one zeroing step, one hashing
step after fixing successful randomness, hole repair, or an entire constituent algorithm. -/
structure Stage (D : TensorialRelation A) where
  run : A → A
  valid (T : A) : D.Rel T (run T)

namespace Stage

variable {D : TensorialRelation A}

/-- The empty transformation. -/
def skip : Stage D where
  run := id
  valid := D.refl

@[simp] theorem skip_run (T : A) : (skip (D := D)).run T = T := rfl

/-- Run `first`, then `second`. -/
def seq (first second : Stage D) : Stage D where
  run T := second.run (first.run T)
  valid T := D.trans (first.valid T) (second.valid (first.run T))

@[simp] theorem seq_run (first second : Stage D) (T : A) :
    (first.seq second).run T = second.run (first.run T) := rfl

/-- Compose a finite sequence of valid tensor transformations. -/
def sequence : List (Stage D) → Stage D
  | [] => skip
  | first :: rest => first.seq (sequence rest)

@[simp] theorem sequence_nil_run (T : A) :
    (sequence ([] : List (Stage D))).run T = T := rfl

@[simp] theorem sequence_cons_run (first : Stage D) (rest : List (Stage D)) (T : A) :
    (sequence (first :: rest)).run T = (sequence rest).run (first.run T) := rfl

/-- Run an asymmetric stage with physical coordinates oriented by `g`: relabel into the logical
coordinates of the stage, run it, and relabel back. -/
def conjugate {G : Type*} [Group G] [MulAction G A]
    (hD : D.IsEquivariant G) (g : G) (stage : Stage D) : Stage D where
  run T := g⁻¹ • stage.run (g • T)
  valid T := by
    have h := hD g⁻¹ (stage.valid (g • T))
    simpa only [inv_smul_smul] using h

@[simp] theorem conjugate_run {G : Type*} [Group G] [MulAction G A]
    (hD : D.IsEquivariant G) (g : G) (stage : Stage D) (T : A) :
    (stage.conjugate hD g).run T = g⁻¹ • stage.run (g • T) := rfl

@[simp] theorem conjugate_one {G : Type*} [Group G] [MulAction G A]
    (hD : D.IsEquivariant G) (stage : Stage D) (T : A) :
    (stage.conjugate hD (1 : G)).run T = stage.run T := by
  simp [conjugate_run]

end Stage

/-- A valid division of one tensor into independently labelled tensor factors. -/
structure LabelledDecomposition (D : TensorialRelation A) (ι : Type v) [Fintype ι] where
  factor : A → ι → A
  valid (T : A) : D.Rel T (∏ i, factor T i)

namespace LabelledDecomposition

variable {D : TensorialRelation A} {ι : Type v} [Fintype ι]

/-- Divide into labelled factors, run an independently oriented stage on every factor, and tensor
the outputs.  The orientation function is arbitrary and may repeat values. -/
noncomputable def assemble {G : Type*} [Group G] [MulAction G A]
    (division : LabelledDecomposition D ι) (hD : D.IsEquivariant G)
    (orientation : ι → G) (stage : ι → Stage D) : Stage D where
  run T := ∏ i, ((stage i).conjugate hD (orientation i)).run (division.factor T i)
  valid T := by
    apply D.trans (division.valid T)
    apply D.fintype_prod
    intro i
    exact ((stage i).conjugate hD (orientation i)).valid (division.factor T i)

@[simp] theorem assemble_run {G : Type*} [Group G] [MulAction G A]
    (division : LabelledDecomposition D ι) (hD : D.IsEquivariant G)
    (orientation : ι → G) (stage : ι → Stage D) (T : A) :
    (division.assemble hD orientation stage).run T =
      ∏ i, (orientation i)⁻¹ • (stage i).run (orientation i • division.factor T i) := by
  simp [assemble, Stage.conjugate_run]

end LabelledDecomposition

/-- The core arbitrary-orientation assembly theorem without an initial division step. -/
theorem arbitrary_labelled_conjugates {G : Type*} [Group G] [MulAction G A]
    {ι : Type v} [Fintype ι] (D : TensorialRelation A) (hD : D.IsEquivariant G)
    (orientation : ι → G) (stage : ι → Stage D) (input : ι → A) :
    D.Rel (∏ i, input i)
      (∏ i, ((stage i).conjugate hD (orientation i)).run (input i)) := by
  apply D.fintype_prod
  intro i
  exact ((stage i).conjugate hD (orientation i)).valid (input i)

/-! ## One-hot time sharing -/

/--
Turn a theorem with one standard slot for every element of `Symmetry` into a theorem for an
arbitrary labelled list of symmetries.

`standardSlot` represents the fixed, pairwise-distinct enumeration used by the original theorem.
`hOneHot r s` is its one-hot specialization: only standard slot `s` is active on labelled input
factor `r`.  For the requested symmetry `orientation r`, choose the unique slot
`standardSlot.symm (orientation r)` and tensor these independently valid instances.

Unlike conjugation, this argument needs no action or equivariance assumption.  Repetitions are
harmless because separate labels invoke separate one-hot instances of the standard theorem.
-/
theorem arbitrary_labels_of_standard_oneHot
    {Slot Symmetry : Type*} {ι : Type v} [Fintype ι]
    (D : TensorialRelation A) (standardSlot : Slot ≃ Symmetry)
    (input : ι → A) (output : ι → Symmetry → A)
    (hOneHot : ∀ r s, D.Rel (input r) (output r (standardSlot s)))
    (orientation : ι → Symmetry) :
    D.Rel (∏ r, input r) (∏ r, output r (orientation r)) := by
  apply D.fintype_prod
  intro r
  simpa using hOneHot r (standardSlot.symm (orientation r))

/-- Derive the one-hot hypotheses from a standard theorem quantified over an admissible parameter
type.  Applications should package all legality conditions into `Parameter`; for example,
`Parameter` can be `ProbabilityVector Slot`, or a family of such vectors indexed by constituent
terms.  The equation `hOneHotOutput` is then the only specialization calculation required. -/
theorem arbitrary_labels_of_standard_parameters
    {Slot Symmetry Parameter : Type*} {ι : Type v} [Fintype ι]
    (D : TensorialRelation A) (standardSlot : Slot ≃ Symmetry)
    (oneHot : Slot → Parameter) (input : ι → A)
    (standardOutput : ι → Parameter → A) (output : ι → Symmetry → A)
    (hStandard : ∀ r parameter, D.Rel (input r) (standardOutput r parameter))
    (hOneHotOutput : ∀ r s,
      standardOutput r (oneHot s) = output r (standardSlot s))
    (orientation : ι → Symmetry) :
    D.Rel (∏ r, input r) (∏ r, output r (orientation r)) := by
  apply D.arbitrary_labels_of_standard_oneHot standardSlot input output
  · intro r s
    rw [← hOneHotOutput r s]
    exact hStandard r (oneHot s)

/-- First divide a tensor into labelled factors and then apply the one-hot time-sharing theorem.
This is the form used by recursive constituent constructions. -/
theorem LabelledDecomposition.arbitrary_labels_of_standard_oneHot
    {Slot Symmetry : Type*} {ι : Type v} [Fintype ι]
    (D : TensorialRelation A) (division : LabelledDecomposition D ι)
    (standardSlot : Slot ≃ Symmetry) (output : ι → Symmetry → A)
    (orientation : ι → Symmetry) (T : A)
    (hOneHot : ∀ r s,
      D.Rel (division.factor T r) (output r (standardSlot s))) :
    D.Rel T (∏ r, output r (orientation r)) := by
  exact D.trans (division.valid T)
    (D.arbitrary_labels_of_standard_oneHot standardSlot
      (division.factor T) output hOneHot orientation)

/-- Divide into labelled factors and derive every oriented factor transformation directly from a
standard theorem quantified over admissible parameters. -/
theorem LabelledDecomposition.arbitrary_labels_of_standard_parameters
    {Slot Symmetry Parameter : Type*} {ι : Type v} [Fintype ι]
    (D : TensorialRelation A) (division : LabelledDecomposition D ι)
    (standardSlot : Slot ≃ Symmetry) (oneHot : Slot → Parameter)
    (standardOutput : A → ι → Parameter → A)
    (output : A → ι → Symmetry → A) (orientation : ι → Symmetry) (T : A)
    (hStandard : ∀ r parameter,
      D.Rel (division.factor T r) (standardOutput T r parameter))
    (hOneHotOutput : ∀ r s,
      standardOutput T r (oneHot s) = output T r (standardSlot s)) :
    D.Rel T (∏ r, output T r (orientation r)) := by
  exact D.trans (division.valid T)
    (D.arbitrary_labels_of_standard_parameters standardSlot oneHot
      (division.factor T) (standardOutput T) (output T)
      hStandard hOneHotOutput orientation)

/-- One recursive level obtained from one-hot specializations of a theorem whose symmetry slots
are fixed by `standardSlot`. -/
structure StandardSlotLevel
    (D : TensorialRelation A) (ι : Type v) [Fintype ι]
    (Slot Symmetry : Type*) (standardSlot : Slot ≃ Symmetry) where
  division : LabelledDecomposition D ι
  orientation : ι → Symmetry
  output : A → ι → Symmetry → A
  oneHot (T : A) (r : ι) (s : Slot) :
    D.Rel (division.factor T r) (output T r (standardSlot s))

/-- Build a recursive standard-slot level from the original theorem quantified over an
admissible parameter type.  This constructor performs the one-hot specialization once and for
all, so downstream recursive composition does not carry a separate one-hot assumption. -/
def StandardSlotLevel.ofStandardParameters
    {ι : Type v} [Fintype ι] {Slot Symmetry Parameter : Type*}
    {standardSlot : Slot ≃ Symmetry} (D : TensorialRelation A)
    (division : LabelledDecomposition D ι) (orientation : ι → Symmetry)
    (oneHot : Slot → Parameter) (standardOutput : A → ι → Parameter → A)
    (output : A → ι → Symmetry → A)
    (hStandard : ∀ T r parameter,
      D.Rel (division.factor T r) (standardOutput T r parameter))
    (hOneHotOutput : ∀ T r s,
      standardOutput T r (oneHot s) = output T r (standardSlot s)) :
    StandardSlotLevel D ι Slot Symmetry standardSlot where
  division := division
  orientation := orientation
  output := output
  oneHot T r s := by
    rw [← hOneHotOutput T r s]
    exact hStandard T r (oneHot s)

namespace StandardSlotLevel

variable {D : TensorialRelation A}
variable {ι : Type v} [Fintype ι] {Slot Symmetry : Type*}
variable {standardSlot : Slot ≃ Symmetry}

/-- The valid global transformation performed by one standard-slot level. -/
noncomputable def stage
    (level : StandardSlotLevel D ι Slot Symmetry standardSlot) : Stage D where
  run T := ∏ r, level.output T r (level.orientation r)
  valid T := LabelledDecomposition.arbitrary_labels_of_standard_oneHot
    D level.division standardSlot (level.output T) level.orientation T (level.oneHot T)

@[simp] theorem stage_run
    (level : StandardSlotLevel D ι Slot Symmetry standardSlot) (T : A) :
    (stage level).run T = ∏ r, level.output T r (level.orientation r) := rfl

/-- Recursively compose levels proved by independent one-hot specializations. -/
noncomputable def recursive
    (levels : List (StandardSlotLevel D ι Slot Symmetry standardSlot)) : Stage D :=
  Stage.sequence (levels.map stage)

/-- Every finite recursion of standard-slot levels is a valid transformation. -/
theorem recursive_valid
    (levels : List (StandardSlotLevel D ι Slot Symmetry standardSlot)) (T : A) :
    D.Rel T ((recursive levels).run T) :=
  (recursive levels).valid T

end StandardSlotLevel

/-- Any finite recursive sequence of valid global or constituent stages remains valid.  In
particular, each stage may itself have been assembled using an unrelated orientation list. -/
theorem recursive_sequence (D : TensorialRelation A) (stages : List (Stage D)) (T : A) :
    D.Rel T (Stage.sequence stages |>.run T) :=
  (Stage.sequence stages).valid T

end TensorialRelation

end AlgebraicComplexity
