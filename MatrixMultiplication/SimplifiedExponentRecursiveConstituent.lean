import AlgebraicComplexity.Analysis.RetainedExponentAggregation
import MatrixMultiplication.SimplifiedExponentRootRecurrence
import Mathlib.Tactic.FinCases

/-!
# Exact dyadic forms for weighted recursive constituent families

The level-three and level-four retained-exponent recurrences have the same local shape.  A local
constituent has an ordered split law, a positive-integer maximum-entropy dual for its logical
`X` branch, and two compatibility-pooling rows for its logical `Y` and `Z` branches.  Its three
rates are then multiplied by an outer dyadic occurrence mass before constituents are summed and
the minimum of the three logical branches is retained.

This module isolates that common, certificate-independent arithmetic.  Concrete generated clients
only need to serialize finite supports, dyadic numerator rows, integer dual factors, and outer
weights.  The main theorem `weightedFamilyBranchForm_eval` proves that the resulting signed-log
form is exactly the real recursive rate; no floating-point or optimizer semantics enter here.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedExponentRecursiveConstituent

open AlgebraicComplexity.RegionalExponent
open AlgebraicComplexity.RetainedExponentAggregation
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRootRecurrence

noncomputable section

/-- A structural support symbol with three coordinates in a common finite alphabet. -/
structure CoordinateTriple (coordinateCount : ℕ) where
  x : Fin coordinateCount
  y : Fin coordinateCount
  z : Fin coordinateCount
  deriving DecidableEq, Repr

/-- List-oriented exact data for one recursive constituent.

The structural support determines the finite state type used by the integer dual.  Reference
numerators are read in the same list order, while `marginalXNumerators` stores their exact
coordinate-`X` pushforward.  A generated validity theorem should establish the support/reference
length and pushforward identities, although `getD 0` makes the semantic function total even before
those checks. -/
structure LocalRows (coordinateCount : ℕ) where
  support : List (CoordinateTriple coordinateCount)
  referenceNumerators : List ℕ
  marginalXNumerators : List ℕ
  weightX : Fin coordinateCount → ℕ
  weightY : Fin coordinateCount → ℕ
  weightZ : Fin coordinateCount → ℕ
  logicalY : CompatibilityRows
  logicalZ : CompatibilityRows

namespace LocalRows

/-- Finite index type of the explicitly serialized support list. -/
abbrev State {coordinateCount : ℕ} (rows : LocalRows coordinateCount) :=
  Fin rows.support.length

/-- Structural support triple stored at one state index. -/
def supportAt {coordinateCount : ℕ} (rows : LocalRows coordinateCount)
    (state : rows.State) : CoordinateTriple coordinateCount :=
  rows.support.get state

/-- Reference-law numerator stored at one state index. -/
def referenceNumerator {coordinateCount : ℕ} (rows : LocalRows coordinateCount)
    (state : rows.State) : ℕ :=
  rows.referenceNumerators[state.val]?.getD 0

/-- Logical `X` coordinate map on the serialized support. -/
def coordinateX {coordinateCount : ℕ} (rows : LocalRows coordinateCount) :
    rows.State → Fin coordinateCount :=
  fun state ↦ (rows.supportAt state).x

/-- Logical `Y` coordinate map on the serialized support. -/
def coordinateY {coordinateCount : ℕ} (rows : LocalRows coordinateCount) :
    rows.State → Fin coordinateCount :=
  fun state ↦ (rows.supportAt state).y

/-- Logical `Z` coordinate map on the serialized support. -/
def coordinateZ {coordinateCount : ℕ} (rows : LocalRows coordinateCount) :
    rows.State → Fin coordinateCount :=
  fun state ↦ (rows.supportAt state).z

/-- Typed root-style view of the list-oriented local data. -/
def toRootRows {coordinateCount : ℕ} (rows : LocalRows coordinateCount) :
    RootRows rows.State (Fin coordinateCount) (Fin coordinateCount) (Fin coordinateCount) :=
  { states := List.ofFn id
    referenceNumerator := rows.referenceNumerator
    referenceList := rows.referenceNumerators
    marginalXList := rows.marginalXNumerators
    weightX := rows.weightX
    weightY := rows.weightY
    weightZ := rows.weightZ
    logicalY := rows.logicalY
    logicalZ := rows.logicalZ }

/-- Common-denominator real rate of one logical branch.  The `X` data use denominator
`2^referenceBits`; compatibility rows use denominator `2^(referenceBits + compatibilityExtraBits)`.
-/
def branchRate {coordinateCount : ℕ} (referenceBits compatibilityExtraBits : ℕ)
    (rows : LocalRows coordinateCount) (branch : Fin 3) : ℝ :=
  rootBranchRate referenceBits (referenceBits + compatibilityExtraBits)
    rows.coordinateX rows.coordinateY rows.coordinateZ rows.toRootRows branch

/-- Semantic local branch in which the logical-`X` maximum entropy has not yet been replaced by
its integer dual.  Compatibility branches are unchanged. -/
def semanticBranchRate {coordinateCount : ℕ}
    (referenceBits compatibilityExtraBits : ℕ)
    (rows : LocalRows coordinateCount) (branch : Fin 3) : ℝ :=
  if branch = 0 then
    rootXSemanticRate referenceBits rows.coordinateX rows.coordinateY rows.coordinateZ
      rows.toRootRows
  else if branch = 1 then
    rows.logicalY.rate (referenceBits + compatibilityExtraBits)
  else
    rows.logicalZ.rate (referenceBits + compatibilityExtraBits)

/-- Certificate-independent validity of one serialized recursive row.  The two list equalities
identify its stored joint and logical-`X` marginal entropy rows with the finite support data. -/
def IsValid {coordinateCount : ℕ} (rows : LocalRows coordinateCount) : Prop :=
  0 < rows.support.length ∧
    rows.referenceNumerators = List.ofFn rows.referenceNumerator ∧
    rows.marginalXNumerators =
      List.ofFn (marginalNumerator rows.coordinateX rows.referenceNumerator) ∧
    (∀ x, 0 < rows.weightX x) ∧
    (∀ y, 0 < rows.weightY y) ∧
    (∀ z, 0 < rows.weightZ z)

/-- Mathematical local branch.  The logical-`X` branch is stated directly using homogeneous
entropy and a fixed-marginal maximum; compatibility branches retain their exact pooled-row
formulas. -/
def mathematicalBranchRate {coordinateCount : ℕ}
    (referenceBits compatibilityExtraBits : ℕ)
    (rows : LocalRows coordinateCount) (branch : Fin 3) : ℝ :=
  if branch = 0 then
    rootXMathematicalRate referenceBits rows.coordinateX rows.coordinateY rows.coordinateZ
      rows.toRootRows
  else if branch = 1 then
    rows.logicalY.rate (referenceBits + compatibilityExtraBits)
  else
    rows.logicalZ.rate (referenceBits + compatibilityExtraBits)

/-- A valid recursive row's integer-dual branch rate is conservative for its mathematical
fixed-marginal rate. -/
theorem branchRate_le_mathematicalBranchRate {coordinateCount : ℕ}
    (referenceBits compatibilityExtraBits : ℕ)
    (rows : LocalRows coordinateCount) (branch : Fin 3)
    (hvalid : rows.IsValid) :
    rows.branchRate referenceBits compatibilityExtraBits branch ≤
      rows.mathematicalBranchRate referenceBits compatibilityExtraBits branch := by
  rcases hvalid with ⟨hsupport, hreference, hmarginal, hweightX, hweightY, hweightZ⟩
  letI : NeZero rows.support.length := ⟨hsupport.ne'⟩
  have hrootValid : rows.toRootRows.IsValid rows.coordinateX :=
    ⟨rfl, hreference, hmarginal, hweightX, hweightY, hweightZ⟩
  fin_cases branch
  · simp only [branchRate, rootBranchRate, Fin.zero_eta, Fin.isValue,
      mathematicalBranchRate, ↓reduceIte]
    exact rootXRate_le_rootXMathematicalRate referenceBits
      rows.coordinateX rows.coordinateY rows.coordinateZ rows.toRootRows hrootValid
  · simp [branchRate, mathematicalBranchRate, rootBranchRate, toRootRows]
  · simp [branchRate, mathematicalBranchRate, rootBranchRate, toRootRows]

/-- Integer-product dual soundness for one recursive constituent. -/
theorem branchRate_le_semanticBranchRate {coordinateCount : ℕ}
    (referenceBits compatibilityExtraBits : ℕ)
    (rows : LocalRows coordinateCount) (branch : Fin 3)
    (hsupport : 0 < rows.support.length)
    (hweightX : ∀ x, 0 < rows.weightX x)
    (hweightY : ∀ y, 0 < rows.weightY y)
    (hweightZ : ∀ z, 0 < rows.weightZ z) :
    rows.branchRate referenceBits compatibilityExtraBits branch ≤
      rows.semanticBranchRate referenceBits compatibilityExtraBits branch := by
  letI : NeZero rows.support.length := ⟨hsupport.ne'⟩
  fin_cases branch
  · simp only [branchRate, rootBranchRate, Fin.zero_eta, Fin.isValue,
      semanticBranchRate, ↓reduceIte]
    exact rootXRate_le_rootXSemanticRate referenceBits
      rows.coordinateX rows.coordinateY rows.coordinateZ rows.toRootRows rfl
      hweightX hweightY hweightZ
  · simp [branchRate, semanticBranchRate, rootBranchRate, toRootRows]
  · simp [branchRate, semanticBranchRate, rootBranchRate, toRootRows]

/-- Exact local branch form at the common compatibility denominator. -/
def branchForm {coordinateCount : ℕ} (referenceBits compatibilityExtraBits : ℕ)
    (rows : LocalRows coordinateCount) (branch : Fin 3) : Form :=
  if branch = 0 then
    rescale compatibilityExtraBits
      (rootXForm referenceBits rows.coordinateX rows.coordinateY rows.coordinateZ
        rows.toRootRows)
  else if branch = 1 then
    rows.logicalY.form (referenceBits + compatibilityExtraBits)
  else
    rows.logicalZ.form (referenceBits + compatibilityExtraBits)

/-- The logical-`X` form depends only on the structural support, the reference and `X`-marginal
rows, and the three dual-weight functions.

In particular, two rows may have completely different logical-`Y` and logical-`Z` compatibility
tables and still have the same branch-zero form.  This projection principle lets generated
certificates check the small root data without elaborating unrelated dense compatibility rows.

Proof sketch: destruct both records, substitute the six relevant field equalities, and reduce the
branch selector at zero.  `rootXForm` never projects either compatibility field. -/
theorem branchForm_zero_congr
    {left right : LocalRows coordinateCount}
    (hsupport : left.support = right.support)
    (hreference : left.referenceNumerators = right.referenceNumerators)
    (hmarginal : left.marginalXNumerators = right.marginalXNumerators)
    (hweightX : left.weightX = right.weightX)
    (hweightY : left.weightY = right.weightY)
    (hweightZ : left.weightZ = right.weightZ)
    (referenceBits compatibilityExtraBits : ℕ) :
    left.branchForm referenceBits compatibilityExtraBits 0 =
      right.branchForm referenceBits compatibilityExtraBits 0 := by
  cases left with
  | mk leftSupport leftReference leftMarginal leftWeightX leftWeightY leftWeightZ
      leftLogicalY leftLogicalZ =>
    cases right with
    | mk rightSupport rightReference rightMarginal rightWeightX rightWeightY rightWeightZ
        rightLogicalY rightLogicalZ =>
      simp only at hsupport hreference hmarginal hweightX hweightY hweightZ
      subst rightSupport
      subst rightReference
      subst rightMarginal
      subst rightWeightX
      subst rightWeightY
      subst rightWeightZ
      rfl

/-- The exact signed-log form evaluates to the selected local semantic branch rate. -/
theorem branchForm_eval {coordinateCount : ℕ}
    (referenceBits compatibilityExtraBits : ℕ)
    (rows : LocalRows coordinateCount) (branch : Fin 3) :
    Form.eval (referenceBits + compatibilityExtraBits)
        (rows.branchForm referenceBits compatibilityExtraBits branch) =
      rows.branchRate referenceBits compatibilityExtraBits branch := by
  fin_cases branch
  · simp only [branchForm, branchRate, Fin.zero_eta, Fin.isValue, ↓reduceIte,
      rootBranchRate]
    rw [rescale_eval, rootXForm_eval]
  · simp [branchForm, branchRate, rootBranchRate, CompatibilityRows.form_eval,
      toRootRows]
  · simp [branchForm, branchRate, rootBranchRate, CompatibilityRows.form_eval,
      toRootRows]

end LocalRows

/-- One local recursive constituent together with its outer dyadic occurrence numerator. -/
structure WeightedLocalRows (coordinateCount : ℕ) where
  outerNumerator : ℕ
  rows : LocalRows coordinateCount

namespace WeightedLocalRows

/-- Semantic local branch contribution after multiplication by its outer occurrence mass. -/
def branchRate {coordinateCount : ℕ} (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entry : WeightedLocalRows coordinateCount) (branch : Fin 3) : ℝ :=
  mass outerBits entry.outerNumerator *
    entry.rows.branchRate referenceBits compatibilityExtraBits branch

/-- Semantic weighted branch before the logical-`X` integer-dual relaxation. -/
def semanticBranchRate {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entry : WeightedLocalRows coordinateCount) (branch : Fin 3) : ℝ :=
  mass outerBits entry.outerNumerator *
    entry.rows.semanticBranchRate referenceBits compatibilityExtraBits branch

/-- Weighted mathematical branch contribution. -/
def mathematicalBranchRate {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entry : WeightedLocalRows coordinateCount) (branch : Fin 3) : ℝ :=
  mass outerBits entry.outerNumerator *
    entry.rows.mathematicalBranchRate referenceBits compatibilityExtraBits branch

theorem branchRate_le_mathematicalBranchRate {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entry : WeightedLocalRows coordinateCount) (branch : Fin 3)
    (hvalid : entry.rows.IsValid) :
    entry.branchRate outerBits referenceBits compatibilityExtraBits branch ≤
      entry.mathematicalBranchRate outerBits referenceBits compatibilityExtraBits branch := by
  exact mul_le_mul_of_nonneg_left
    (LocalRows.branchRate_le_mathematicalBranchRate referenceBits compatibilityExtraBits
      entry.rows branch hvalid) (by
        unfold mass
        positivity)

theorem branchRate_le_semanticBranchRate {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entry : WeightedLocalRows coordinateCount) (branch : Fin 3)
    (hsupport : 0 < entry.rows.support.length)
    (hweightX : ∀ x, 0 < entry.rows.weightX x)
    (hweightY : ∀ y, 0 < entry.rows.weightY y)
    (hweightZ : ∀ z, 0 < entry.rows.weightZ z) :
    entry.branchRate outerBits referenceBits compatibilityExtraBits branch ≤
      entry.semanticBranchRate outerBits referenceBits compatibilityExtraBits branch := by
  exact mul_le_mul_of_nonneg_left
    (LocalRows.branchRate_le_semanticBranchRate referenceBits compatibilityExtraBits
      entry.rows branch hsupport hweightX hweightY hweightZ) (by
        unfold mass
        positivity)

/-- Exact form for the outer-mass-weighted local branch. -/
def branchForm {coordinateCount : ℕ} (referenceBits compatibilityExtraBits : ℕ)
    (entry : WeightedLocalRows coordinateCount) (branch : Fin 3) : Form :=
  Form.scaleNat entry.outerNumerator
    (entry.rows.branchForm referenceBits compatibilityExtraBits branch)

/-- Evaluating the weighted form at the combined denominator gives the weighted branch rate. -/
theorem branchForm_eval {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entry : WeightedLocalRows coordinateCount) (branch : Fin 3) :
    Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
        (entry.branchForm referenceBits compatibilityExtraBits branch) =
      entry.branchRate outerBits referenceBits compatibilityExtraBits branch := by
  rw [branchForm, scaleNat_eval_add_bits, LocalRows.branchForm_eval]
  rfl

end WeightedLocalRows

/-- Sum of one logical branch across a list of weighted local constituents. -/
def weightedFamilyBranchRate {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) (branch : Fin 3) : ℝ :=
  (entries.map fun entry ↦
    entry.branchRate outerBits referenceBits compatibilityExtraBits branch).sum

/-- Semantic branch sum over a weighted local family. -/
def semanticWeightedFamilyBranchRate {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) (branch : Fin 3) : ℝ :=
  (entries.map fun entry ↦
    entry.semanticBranchRate outerBits referenceBits compatibilityExtraBits branch).sum

/-- Mathematical branch sum over a weighted local family. -/
def mathematicalWeightedFamilyBranchRate {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) (branch : Fin 3) : ℝ :=
  (entries.map fun entry ↦
    entry.mathematicalBranchRate outerBits referenceBits compatibilityExtraBits branch).sum

/-- Valid serialized rows give a conservative exact family rate. -/
theorem weightedFamilyBranchRate_le_mathematical
    {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) (branch : Fin 3)
    (hvalid : ∀ entry ∈ entries, entry.rows.IsValid) :
    weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits entries branch ≤
      mathematicalWeightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
        entries branch := by
  induction entries with
  | nil => simp [weightedFamilyBranchRate, mathematicalWeightedFamilyBranchRate]
  | cons entry entries ih =>
      simp only [weightedFamilyBranchRate, mathematicalWeightedFamilyBranchRate,
        List.map_cons, List.sum_cons]
      apply add_le_add
      · exact WeightedLocalRows.branchRate_le_mathematicalBranchRate
          outerBits referenceBits compatibilityExtraBits entry branch
            (hvalid entry (by simp))
      · apply ih
        intro tail htail
        exact hvalid tail (by simp [htail])

/-- Pointwise valid integer duals give a lower bound for the semantic family branch. -/
theorem weightedFamilyBranchRate_le_semantic
    {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) (branch : Fin 3)
    (hsupport : ∀ entry ∈ entries, 0 < entry.rows.support.length)
    (hweightX : ∀ entry ∈ entries, ∀ x, 0 < entry.rows.weightX x)
    (hweightY : ∀ entry ∈ entries, ∀ y, 0 < entry.rows.weightY y)
    (hweightZ : ∀ entry ∈ entries, ∀ z, 0 < entry.rows.weightZ z) :
    weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits entries branch ≤
      semanticWeightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
        entries branch := by
  induction entries with
  | nil => simp [weightedFamilyBranchRate, semanticWeightedFamilyBranchRate]
  | cons entry entries ih =>
      simp only [weightedFamilyBranchRate, semanticWeightedFamilyBranchRate,
        List.map_cons, List.sum_cons]
      apply add_le_add
      · exact WeightedLocalRows.branchRate_le_semanticBranchRate
          outerBits referenceBits compatibilityExtraBits entry branch
            (hsupport entry (by simp))
            (hweightX entry (by simp)) (hweightY entry (by simp))
            (hweightZ entry (by simp))
      · apply ih
        · intro tail htail
          exact hsupport tail (by simp [htail])
        · intro tail htail
          exact hweightX tail (by simp [htail])
        · intro tail htail
          exact hweightY tail (by simp [htail])
        · intro tail htail
          exact hweightZ tail (by simp [htail])

/-- Exact signed-log form for one branch of a weighted local family. -/
def weightedFamilyBranchForm {coordinateCount : ℕ}
    (referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) (branch : Fin 3) : Form :=
  Form.sum (entries.map fun entry ↦
    entry.branchForm referenceBits compatibilityExtraBits branch)

/-- The summed exact form evaluates to the semantic branch sum over the complete family. -/
theorem weightedFamilyBranchForm_eval {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) (branch : Fin 3) :
    Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)
        (weightedFamilyBranchForm referenceBits compatibilityExtraBits entries branch) =
      weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits entries branch := by
  rw [weightedFamilyBranchForm, Form.eval_sum]
  unfold weightedFamilyBranchRate
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry _
  exact WeightedLocalRows.branchForm_eval outerBits referenceBits compatibilityExtraBits
    entry branch

/-- Branch rates are additive under concatenation of constituent lists. -/
theorem weightedFamilyBranchRate_append {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (left right : List (WeightedLocalRows coordinateCount)) (branch : Fin 3) :
    weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
        (left ++ right) branch =
      weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits left branch +
        weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits right branch := by
  simp [weightedFamilyBranchRate]

/-- Split a weighted family into certificate-sized chunks without changing its semantic rate. -/
theorem weightedFamilyBranchRate_flatten {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (chunks : List (List (WeightedLocalRows coordinateCount))) (branch : Fin 3) :
    weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
        chunks.flatten branch =
      (chunks.map fun entries ↦
        weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits
          entries branch).sum := by
  induction chunks with
  | nil => rfl
  | cons entries chunks ih =>
      simp only [List.flatten_cons, List.map_cons, List.sum_cons]
      rw [weightedFamilyBranchRate_append, ih]

/-- Retained exponent of one weighted local family. -/
def weightedFamilyRetainedExponent {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) : ℝ :=
  threeWayMin
    (weightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits entries)

/-- Semantic retained exponent of a weighted local family. -/
def semanticWeightedFamilyRetainedExponent {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) : ℝ :=
  threeWayMin
    (semanticWeightedFamilyBranchRate outerBits referenceBits compatibilityExtraBits entries)

/-- Mathematical retained exponent of a valid weighted local family. -/
def mathematicalWeightedFamilyRetainedExponent {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount)) : ℝ :=
  threeWayMin
    (mathematicalWeightedFamilyBranchRate outerBits referenceBits
      compatibilityExtraBits entries)

theorem weightedFamilyRetainedExponent_le_mathematical
    {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount))
    (hvalid : ∀ entry ∈ entries, entry.rows.IsValid) :
    weightedFamilyRetainedExponent outerBits referenceBits compatibilityExtraBits entries ≤
      mathematicalWeightedFamilyRetainedExponent outerBits referenceBits
        compatibilityExtraBits entries := by
  apply threeWayMin_mono
  intro branch
  exact weightedFamilyBranchRate_le_mathematical outerBits referenceBits
    compatibilityExtraBits entries branch hvalid

theorem weightedFamilyRetainedExponent_le_semantic
    {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : List (WeightedLocalRows coordinateCount))
    (hsupport : ∀ entry ∈ entries, 0 < entry.rows.support.length)
    (hweightX : ∀ entry ∈ entries, ∀ x, 0 < entry.rows.weightX x)
    (hweightY : ∀ entry ∈ entries, ∀ y, 0 < entry.rows.weightY y)
    (hweightZ : ∀ entry ∈ entries, ∀ z, 0 < entry.rows.weightZ z) :
    weightedFamilyRetainedExponent outerBits referenceBits compatibilityExtraBits entries ≤
      semanticWeightedFamilyRetainedExponent outerBits referenceBits
        compatibilityExtraBits entries := by
  apply threeWayMin_mono
  intro branch
  exact weightedFamilyBranchRate_le_semantic outerBits referenceBits
    compatibilityExtraBits entries branch hsupport hweightX hweightY hweightZ

/-- Total retained exponent across a finite family of regions. -/
def regionalRetainedExponent {Region : Type*} [Fintype Region]
    {coordinateCount : ℕ}
    (outerBits referenceBits compatibilityExtraBits : ℕ)
    (entries : Region → List (WeightedLocalRows coordinateCount)) : ℝ :=
  ∑ region, weightedFamilyRetainedExponent outerBits referenceBits compatibilityExtraBits
    (entries region)

end

end MatrixMultiplication.SimplifiedExponentRecursiveConstituent
