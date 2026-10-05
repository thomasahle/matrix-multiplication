import AlgebraicComplexity.Analysis.RegionalExponent
import AlgebraicComplexity.MatrixMultiplication.LevelFourReconstruction
import MatrixMultiplication.CompatibilityRowsForm
import MatrixMultiplication.HomogeneousIntegerEntropyDualForm
import MatrixMultiplication.SignedDyadicLogCanonical
import Mathlib.Tactic.FinCases

/-!
# Root-family retained-exponent recurrence

This module formalizes the root part of the retained-exponent recurrence used by the simplified
level-four certificate.  It is deliberately data-parametric: generated clients supply the exact
dyadic rows, support coordinates, and positive integer dual factors.

The logical `X` branch is the marginal entropy minus combination loss,

`H(X) + H(reference) - homogeneousDual(reference)`.

The logical `Y` and `Z` branches use the compatibility formula

`H(pooled) - ∑ H(first rows) - ∑ H(compatibility-cell rows)`.

All three formulas are represented by exact signed-log forms, and the evaluation theorems below
prove their equality to the corresponding real entropy expressions.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedExponentRootRecurrence

open AlgebraicComplexity
open AlgebraicComplexity.RegionalExponent
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.EntropyDual
open MatrixMultiplication.HomogeneousEntropyDual
open MatrixMultiplication.HomogeneousIntegerEntropyDualForm
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

variable {A X Y Z : Type*}

/-! ## Concrete total-sixteen root support -/

/-- Number of nonnegative triples with coordinate sum sixteen. -/
def rootShapeCount : ℕ := 153

theorem shapes_sixteen_length : (shapes 16).length = rootShapeCount := by
  set_option maxRecDepth 100000 in
    decide

/-- Certificate-order total-sixteen shape. -/
def rootShape (index : Fin rootShapeCount) : Shape :=
  (shapes 16).get ⟨index.val, by
    rw [shapes_sixteen_length]
    exact index.isLt⟩

theorem rootShape_total (index : Fin rootShapeCount) : (rootShape index).total = 16 := by
  unfold rootShape
  exact mem_shapes_total (List.get_mem (shapes 16) _)

/-- One root-shape coordinate, represented in the exact range `0,…,16`. -/
def rootCoordinate (coordinate : Fin 3) (index : Fin rootShapeCount) : Fin 17 :=
  match coordinate with
  | ⟨0, _⟩ => ⟨(rootShape index).x, by
      have h := rootShape_total index
      simp only [Shape.total] at h
      omega⟩
  | ⟨1, _⟩ => ⟨(rootShape index).y, by
      have h := rootShape_total index
      simp only [Shape.total] at h
      omega⟩
  | ⟨2, _⟩ => ⟨(rootShape index).z, by
      have h := rootShape_total index
      simp only [Shape.total] at h
      omega⟩

/-- Exact data needed for one root orientation. -/
structure RootRows (A X Y Z : Type*) where
  states : List A
  referenceNumerator : A → ℕ
  referenceList : List ℕ
  marginalXList : List ℕ
  weightX : X → ℕ
  weightY : Y → ℕ
  weightZ : Z → ℕ
  logicalY : CompatibilityRows
  logicalZ : CompatibilityRows

namespace RootRows

/-- Structural and dual-witness validity for a finite-indexed root row.  The list equalities are
the executable boundary: they prove that the serialized entropy rows enumerate precisely the
reference law and its logical-`X` marginal. -/
def IsValid
    {n xCount yCount zCount : ℕ}
    (coordX : Fin n → Fin xCount)
    (rows : RootRows (Fin n) (Fin xCount) (Fin yCount) (Fin zCount)) : Prop :=
  rows.states = List.ofFn id ∧
    rows.referenceList = List.ofFn rows.referenceNumerator ∧
    rows.marginalXList =
      List.ofFn (marginalNumerator coordX rows.referenceNumerator) ∧
    (∀ x, 0 < rows.weightX x) ∧
    (∀ y, 0 < rows.weightY y) ∧
    (∀ z, 0 < rows.weightZ z)

end RootRows

/-- Real logical-`X` root branch: marginal entropy minus the certified combination-loss dual
gap. -/
def rootXRate
    (bits : ℕ) (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : RootRows A X Y Z) : ℝ :=
  weightedEntropyList bits rows.marginalXList +
    weightedEntropyList bits rows.referenceList -
    homogeneousIntegerDualBitsOn bits rows.states rows.referenceNumerator coordX coordY coordZ
      rows.weightX rows.weightY rows.weightZ

/-- Semantic logical-`X` branch before replacing its homogeneous maximum entropy by an integer
product-family dual.  The two supplied entropy rows are kept list-oriented; separate structural
validity lemmas identify them with the reference row and its logical-`X` pushforward. -/
def rootXSemanticRate
    {n : ℕ} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (coordX : Fin n → X) (coordY : Fin n → Y) (coordZ : Fin n → Z)
    (rows : RootRows (Fin n) X Y Z) : ℝ :=
  weightedEntropyList bits rows.marginalXList +
    weightedEntropyList bits rows.referenceList -
    maximumHomogeneousEntropyBits coordX coordY coordZ
      (fun state ↦ mass bits (rows.referenceNumerator state))

/-- Mathematical logical-`X` rate, stated directly in terms of the dyadic reference mass, its
coordinate marginal, and the supremal homogeneous entropy in the fixed three-marginal fiber. -/
def rootXMathematicalRate
    {n : ℕ} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (coordX : Fin n → X) (coordY : Fin n → Y) (coordZ : Fin n → Z)
    (rows : RootRows (Fin n) X Y Z) : ℝ :=
  homogeneousEntropyBits
      (marginal coordX (fun state ↦ mass bits (rows.referenceNumerator state))) +
    homogeneousEntropyBits (fun state ↦ mass bits (rows.referenceNumerator state)) -
    maximumHomogeneousEntropyBits coordX coordY coordZ
      (fun state ↦ mass bits (rows.referenceNumerator state))

/-- A structurally valid serialization has exactly the mathematical logical-`X` semantic rate. -/
theorem rootXSemanticRate_eq_rootXMathematicalRate
    {n xCount yCount zCount : ℕ}
    (bits : ℕ)
    (coordX : Fin n → Fin xCount) (coordY : Fin n → Fin yCount)
    (coordZ : Fin n → Fin zCount)
    (rows : RootRows (Fin n) (Fin xCount) (Fin yCount) (Fin zCount))
    (hvalid : rows.IsValid coordX) :
    rootXSemanticRate bits coordX coordY coordZ rows =
      rootXMathematicalRate bits coordX coordY coordZ rows := by
  rcases hvalid with ⟨_hstates, hreference, hmarginal, _hweightX, _hweightY,
    _hweightZ⟩
  have hmarginalMass :
      (fun x ↦ mass bits (marginalNumerator coordX rows.referenceNumerator x)) =
        marginal coordX (fun state ↦ mass bits (rows.referenceNumerator state)) := by
    funext x
    exact (marginal_dyadic bits rows.referenceNumerator coordX x).symm
  unfold rootXSemanticRate rootXMathematicalRate
  rw [hreference, hmarginal,
    weightedEntropyList_ofFn_eq_weightedEntropy,
    weightedEntropyList_ofFn_eq_weightedEntropy,
    weightedEntropy_dyadic_eq_homogeneousEntropyBits,
    weightedEntropy_dyadic_eq_homogeneousEntropyBits,
    hmarginalMass]

/-- Soundness of a generated integer dual for the logical-`X` branch.  No optimizer convergence
is assumed: positivity of the serialized integer factors is sufficient. -/
theorem rootXRate_le_rootXSemanticRate
    {n : ℕ} [NeZero n] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (bits : ℕ) (coordX : Fin n → X) (coordY : Fin n → Y) (coordZ : Fin n → Z)
    (rows : RootRows (Fin n) X Y Z)
    (hstates : rows.states = List.ofFn id)
    (hweightX : ∀ x, 0 < rows.weightX x)
    (hweightY : ∀ y, 0 < rows.weightY y)
    (hweightZ : ∀ z, 0 < rows.weightZ z) :
    rootXRate bits coordX coordY coordZ rows ≤
      rootXSemanticRate bits coordX coordY coordZ rows := by
  have hdual :=
    maximumHomogeneousEntropyBits_dyadic_le_homogeneousIntegerDualBits_of_nonnegative
    bits rows.referenceNumerator coordX coordY coordZ
      rows.weightX rows.weightY rows.weightZ hweightX hweightY hweightZ
  unfold rootXRate rootXSemanticRate
  rw [hstates, homogeneousIntegerDualBitsOn_fin_eq]
  linarith

/-- End-to-end soundness of a structurally valid serialized root row: the exact integer-dual
rate is a lower bound for the mathematical fixed-marginal type-counting rate. -/
theorem rootXRate_le_rootXMathematicalRate
    {n xCount yCount zCount : ℕ} [NeZero n]
    (bits : ℕ)
    (coordX : Fin n → Fin xCount) (coordY : Fin n → Fin yCount)
    (coordZ : Fin n → Fin zCount)
    (rows : RootRows (Fin n) (Fin xCount) (Fin yCount) (Fin zCount))
    (hvalid : rows.IsValid coordX) :
    rootXRate bits coordX coordY coordZ rows ≤
      rootXMathematicalRate bits coordX coordY coordZ rows := by
  rcases hvalid with ⟨hstates, hreference, hmarginal, hweightX, hweightY, hweightZ⟩
  have hsemantic := rootXRate_le_rootXSemanticRate bits coordX coordY coordZ rows
    hstates hweightX hweightY hweightZ
  exact hsemantic.trans_eq
    (rootXSemanticRate_eq_rootXMathematicalRate bits coordX coordY coordZ rows
      ⟨hstates, hreference, hmarginal, hweightX, hweightY, hweightZ⟩)

/-- Exact signed-log form of the logical-`X` root branch. -/
def rootXForm
    (bits : ℕ) (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : RootRows A X Y Z) : Form :=
  Form.sub
    (Form.add
      (weightedEntropyForm bits rows.marginalXList)
      (weightedEntropyForm bits rows.referenceList))
    (homogeneousIntegerDualFormOn rows.states rows.referenceNumerator coordX coordY coordZ
      rows.weightX rows.weightY rows.weightZ)

theorem rootXForm_eval
    (bits : ℕ) (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : RootRows A X Y Z) :
    Form.eval bits (rootXForm bits coordX coordY coordZ rows) =
      rootXRate bits coordX coordY coordZ rows := by
  rw [rootXForm, Form.eval_sub, Form.eval_add,
    weightedEntropyForm_eval, weightedEntropyForm_eval,
    homogeneousIntegerDualFormOn_eval]
  rfl

/-- The three root branches.  The compatibility rows may use a larger common denominator than
the top reference row, as happens after recursively constructing complete-split child laws. -/
def rootBranchRate
    (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : RootRows A X Y Z) (branch : Fin 3) : ℝ :=
  if branch = 0 then rootXRate topBits coordX coordY coordZ rows
  else if branch = 1 then rows.logicalY.rate childBits
  else rows.logicalZ.rate childBits

/-- Exact form for one root branch, returned together with its denominator bit count. -/
def rootBranchForm
    (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : RootRows A X Y Z) (branch : Fin 3) : ℕ × Form :=
  if branch = 0 then (topBits, rootXForm topBits coordX coordY coordZ rows)
  else if branch = 1 then (childBits, rows.logicalY.form childBits)
  else (childBits, rows.logicalZ.form childBits)

theorem rootBranchForm_eval
    (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : RootRows A X Y Z) (branch : Fin 3) :
    Form.eval (rootBranchForm topBits childBits coordX coordY coordZ rows branch).1
        (rootBranchForm topBits childBits coordX coordY coordZ rows branch).2 =
      rootBranchRate topBits childBits coordX coordY coordZ rows branch := by
  fin_cases branch
  · simp [rootBranchForm, rootBranchRate, rootXForm_eval]
  · simp [rootBranchForm, rootBranchRate, CompatibilityRows.form_eval]
  · simp [rootBranchForm, rootBranchRate, CompatibilityRows.form_eval]

/-- Retained exponent of one root orientation. -/
def rootRetainedExponent
    (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : RootRows A X Y Z) : ℝ :=
  threeWayMin (rootBranchRate topBits childBits coordX coordY coordZ rows)

/-- Total retained exponent of a finite root-orientation family. -/
def rootFamilyRetainedExponent
    {Root : Type*} [Fintype Root]
    (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : Root → RootRows A X Y Z) : ℝ :=
  ∑ root, rootRetainedExponent topBits childBits coordX coordY coordZ (rows root)

end

end MatrixMultiplication.SimplifiedExponentRootRecurrence
