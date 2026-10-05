import AlgebraicComplexity.MatrixMultiplication.LevelFourZeroLawGeometry
import AlgebraicComplexity.Probability.DyadicTable

/-!
# Exact schemas for the remaining level-four certificate arrays

This paper-client module describes the non-floating-point arrays not covered by the positive
level-three adapter:

* the joint top mass (`top_zero_num` together with `top_branch_num`);
* the active level-two edge zero laws (`edge_zero2_num`);
* the level-three zero-law rows (`zero3_num`);
* the level-four zero-law rows (`zero4_num`);
* the open-interval constraints on `mu_num`.

The support widths are reconstructed from constituent shapes.  Zero-law arrays are stored in
ragged form: the archived evaluator pads level-two, level-three, and level-four rows to widths
`3`, `19`, and `1107`, but every padded coordinate is required to be zero.  Omitting those zeros
keeps the generated Lean source and its kernel check substantially smaller without changing the
probability law consumed by the recurrence.

Concrete numerators remain in opt-in generated modules.  This file contains only schemas,
indexing conventions, and reusable exact adapters.
-/

open scoped BigOperators

namespace MatrixMultiplication.LevelFourRemainingReconstruction

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000

/-- Bit width shared by every primary probability table in the archived certificate. -/
def bits : ℕ := 32

/-- Number of ordered level-three shape pairs used at the top recursive node. -/
def topPairCount : ℕ := 1785

/-- Expand a sum over six indices without unfolding the summand.  Generated certificate proofs
use this small structural lemma to assemble prechecked row totals cheaply. -/
theorem sum_fin_six (f : Fin 6 → ℕ) :
    (∑ region, f region) =
      f ⟨0, by decide⟩ +
        (f ⟨1, by decide⟩ +
          (f ⟨2, by decide⟩ +
            (f ⟨3, by decide⟩ + (f ⟨4, by decide⟩ + f ⟨5, by decide⟩)))) := by
  simp [Fin.sum_univ_succ]

/-- Region-indexed specialization of `sum_fin_six`. -/
theorem sum_regions_six (f : Fin regionCount → ℕ) :
    (∑ region, f region) =
      f ⟨0, by decide⟩ +
        (f ⟨1, by decide⟩ +
          (f ⟨2, by decide⟩ +
            (f ⟨3, by decide⟩ + (f ⟨4, by decide⟩ + f ⟨5, by decide⟩)))) := by
  unfold regionCount at f ⊢
  exact sum_fin_six f

/-- Atom indexing one top-level zero shape. -/
abbrev TopZeroAtom := Fin regionCount × Fin zeroFourShapeCount

/-- Atom indexing one positive top branch. -/
abbrev TopBranchAtom := Fin regionCount × (Fin regionCount × Fin topPairCount)

/-- The disjoint union forming the global top distribution. -/
abbrev TopAtom := TopZeroAtom ⊕ TopBranchAtom

/-- Nested exact arrays for the joint top distribution. -/
structure TopMassArrays where
  zero : Array (Array ℕ)
  branch : Array (Array (Array ℕ))

namespace TopMassArrays

/-- Exact expected dimensions of the nested arrays. -/
def HasShape (data : TopMassArrays) : Prop :=
  data.zero.size = regionCount ∧
  (∀ root : Fin regionCount, (data.zero[root.val]?.getD #[]).size = zeroFourShapeCount) ∧
  data.branch.size = regionCount ∧
  (∀ root : Fin regionCount, (data.branch[root.val]?.getD #[]).size = regionCount) ∧
  (∀ (root : Fin regionCount) (region : Fin regionCount),
    ((data.branch[root.val]?.getD #[])[region.val]?.getD #[]).size = topPairCount)

instance (data : TopMassArrays) : Decidable data.HasShape := by
  unfold HasShape
  infer_instance

def numerator (data : TopMassArrays) : TopAtom → ℕ
  | .inl (root, shape) =>
      (data.zero[root.val]?.getD #[])[shape.val]?.getD 0
  | .inr (root, region, pair) =>
      ((data.branch[root.val]?.getD #[])[region.val]?.getD #[])[pair.val]?.getD 0

def zeroRowTotal (data : TopMassArrays) (root : Fin regionCount) : ℕ :=
  ∑ shape, data.numerator (.inl (root, shape))

def branchRowTotal (data : TopMassArrays)
    (root region : Fin regionCount) : ℕ :=
  ∑ pair, data.numerator (.inr (root, region, pair))

/-- Sum of the top numerators, arranged in the same nested form as the source arrays. -/
def totalNumerator (data : TopMassArrays) : ℕ :=
  (∑ root, data.zeroRowTotal root) +
    ∑ root, ∑ region, data.branchRowTotal root region

/-- Expose the nested row-total form without unfolding a concrete array literal.  Keeping this
identity opaque prevents aggregate certificate proofs from normalizing every serialized entry a
second time after the individual row checks have already done so. -/
theorem totalNumerator_eq_rowTotals (data : TopMassArrays) :
    data.totalNumerator =
      (∑ root, data.zeroRowTotal root) +
        ∑ root, ∑ region, data.branchRowTotal root region := by
  rfl

/-- Interpret the two top arrays as one dyadic mass. -/
def toDyadicMass (data : TopMassArrays) : DyadicMassData TopAtom :=
  ⟨data.numerator⟩

/-- Exact top feasibility: one globally normalized joint mass.  `HasShape` is a separate
serialization check; extra serialized coordinates cannot affect this semantic mass. -/
def IsValid (data : TopMassArrays) : Prop :=
  data.totalNumerator = dyadicDenominator bits

instance (data : TopMassArrays) : Decidable data.IsValid := by
  unfold IsValid
  infer_instance

def toRational (data : TopMassArrays) : RationalProbabilityData TopAtom :=
  data.toDyadicMass.toRational bits

theorem toRational_isProbability {data : TopMassArrays} (hdata : data.IsValid) :
    data.toRational.IsProbability := by
  have htotal : data.totalNumerator = dyadicDenominator bits := by
    simpa only [IsValid] using hdata
  apply DyadicMassData.toRational_isProbability
  unfold DyadicMassData.IsProbability
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  simpa only [totalNumerator, zeroRowTotal, branchRowTotal, toDyadicMass] using htotal

end TopMassArrays

/-- Ragged exact arrays for active level-two edge zero laws. -/
structure EdgeZeroArrays where
  numerator : Array (Array (Array (Array ℕ)))

namespace EdgeZeroArrays

private def rowArray (data : EdgeZeroArrays) (node : Fin nodeCount)
    (region : Fin regionCount) (slot : Fin splitSlotCount) : Array ℕ :=
  (((data.numerator[node.val]?.getD #[])[region.val]?.getD #[])[slot.val]?.getD #[])

/-- Array shape, including empty rows at invalid padded split positions. -/
def HasShape (data : EdgeZeroArrays) : Prop :=
  data.numerator.size = nodeCount ∧
  (∀ node : Fin nodeCount, (data.numerator[node.val]?.getD #[]).size = regionCount) ∧
  (∀ (node : Fin nodeCount) (region : Fin regionCount),
    ((data.numerator[node.val]?.getD #[])[region.val]?.getD #[]).size = splitSlotCount) ∧
  (∀ (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount),
    (data.rowArray node region slot).size =
      if h : splitSlotValid node slot then edgeZeroWidth ⟨(node, region, slot), h⟩ else 0)

instance (data : EdgeZeroArrays) : Decidable data.HasShape := by
  unfold HasShape
  infer_instance

def toDyadicTable (data : EdgeZeroArrays) : DyadicTable EdgeZeroRow edgeZeroWidth where
  numerator row symbol :=
    (data.rowArray row.node row.region row.slot)[symbol.val]?.getD 0

def IsValid (data : EdgeZeroArrays) : Prop :=
  data.toDyadicTable.IsProbability bits

instance (data : EdgeZeroArrays) : Decidable data.IsValid := by
  unfold IsValid DyadicTable.IsProbability
  infer_instance

def rowToRational (data : EdgeZeroArrays) (row : EdgeZeroRow) :=
  data.toDyadicTable.rowToRational bits row

theorem rowToRational_isProbability {data : EdgeZeroArrays} (hdata : data.IsValid)
    (row : EdgeZeroRow) : (data.rowToRational row).IsProbability :=
  DyadicTable.rowToRational_isProbability hdata row

end EdgeZeroArrays

/-- Ragged exact arrays for all 270 level-three shape/region rows. -/
structure ZeroThreeArrays where
  numerator : Array (Array ℕ)

namespace ZeroThreeArrays

def HasShape (data : ZeroThreeArrays) : Prop :=
  data.numerator.size = zeroThreeRowCount ∧
  ∀ row : Fin zeroThreeRowCount,
    (data.numerator[row.val]?.getD #[]).size = zeroThreeWidth row

instance (data : ZeroThreeArrays) : Decidable data.HasShape := by
  unfold HasShape
  infer_instance

def toDyadicTable (data : ZeroThreeArrays) :
    DyadicTable (Fin zeroThreeRowCount) zeroThreeWidth where
  numerator row symbol := (data.numerator[row.val]?.getD #[])[symbol.val]?.getD 0

def IsValid (data : ZeroThreeArrays) : Prop :=
  data.toDyadicTable.IsProbability bits

instance (data : ZeroThreeArrays) : Decidable data.IsValid := by
  unfold IsValid DyadicTable.IsProbability
  infer_instance

def rowToRational (data : ZeroThreeArrays) (row : Fin zeroThreeRowCount) :=
  data.toDyadicTable.rowToRational bits row

theorem rowToRational_isProbability {data : ZeroThreeArrays} (hdata : data.IsValid)
    (row : Fin zeroThreeRowCount) : (data.rowToRational row).IsProbability :=
  DyadicTable.rowToRational_isProbability hdata row

end ZeroThreeArrays

/-- Ragged exact arrays for six incoming copies of every level-four zero shape. -/
structure ZeroFourArrays where
  numerator : Array (Array (Array ℕ))

namespace ZeroFourArrays

private def rowArray (data : ZeroFourArrays) (row : ZeroFourRow) : Array ℕ :=
  (data.numerator[row.1.val]?.getD #[])[row.2.val]?.getD #[]

def HasShape (data : ZeroFourArrays) : Prop :=
  data.numerator.size = regionCount ∧
  (∀ root : Fin regionCount,
    (data.numerator[root.val]?.getD #[]).size = zeroFourShapeCount) ∧
  ∀ row : ZeroFourRow, (data.rowArray row).size = zeroFourWidth row

instance (data : ZeroFourArrays) : Decidable data.HasShape := by
  unfold HasShape
  infer_instance

def toDyadicTable (data : ZeroFourArrays) : DyadicTable ZeroFourRow zeroFourWidth where
  numerator row symbol := (data.rowArray row)[symbol.val]?.getD 0

def IsValid (data : ZeroFourArrays) : Prop :=
  data.toDyadicTable.IsProbability bits

instance (data : ZeroFourArrays) : Decidable data.IsValid := by
  unfold IsValid DyadicTable.IsProbability
  infer_instance

def rowToRational (data : ZeroFourArrays) (row : ZeroFourRow) :=
  data.toDyadicTable.rowToRational bits row

theorem rowToRational_isProbability {data : ZeroFourArrays} (hdata : data.IsValid)
    (row : ZeroFourRow) : (data.rowToRational row).IsProbability :=
  DyadicTable.rowToRational_isProbability hdata row

end ZeroFourArrays

/-- Exact `mu_num` array used on level-two positive edges. -/
structure MuArrays where
  numerator : Array (Array (Array ℕ))

namespace MuArrays

private def value (data : MuArrays) (node : Fin nodeCount)
    (region : Fin regionCount) (slot : Fin splitSlotCount) : ℕ :=
  ((data.numerator[node.val]?.getD #[])[region.val]?.getD #[])[slot.val]?.getD 0

/-- Public semantic accessor for one stored level-two `mu` numerator.  The nested-array fallback
is retained from the executable certificate schema; `IsValid` proves that every requested entry
lies in the open interval `(0, 2^31)`. -/
def muNumerator (data : MuArrays) (node : Fin nodeCount)
    (region : Fin regionCount) (slot : Fin splitSlotCount) : ℕ :=
  data.value node region slot

/-- Dimensions and the exact open interval `0 < μ < 1/2` for every stored dyadic parameter. -/
def IsValid (data : MuArrays) : Prop :=
  data.numerator.size = nodeCount ∧
  (∀ node : Fin nodeCount, (data.numerator[node.val]?.getD #[]).size = regionCount) ∧
  (∀ (node : Fin nodeCount) (region : Fin regionCount),
    ((data.numerator[node.val]?.getD #[])[region.val]?.getD #[]).size = splitSlotCount) ∧
  ∀ (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount),
    0 < data.value node region slot ∧
      data.value node region slot < dyadicDenominator bits / 2

instance (data : MuArrays) : Decidable data.IsValid := by
  unfold IsValid
  infer_instance

/-- A valid certificate gives a strictly positive numerator at every level-two slot. -/
theorem muNumerator_pos {data : MuArrays} (hdata : data.IsValid)
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) :
    0 < data.muNumerator node region slot := by
  exact (hdata.2.2.2 node region slot).1

/-- A valid certificate puts every level-two numerator strictly below one half of its dyadic
denominator. -/
theorem muNumerator_lt_half {data : MuArrays} (hdata : data.IsValid)
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) :
    data.muNumerator node region slot < dyadicDenominator bits / 2 := by
  exact (hdata.2.2.2 node region slot).2

end MuArrays

end MatrixMultiplication.LevelFourRemainingReconstruction
