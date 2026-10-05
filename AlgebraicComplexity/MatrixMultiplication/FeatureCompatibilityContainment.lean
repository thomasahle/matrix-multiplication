import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibility

/-!
# Containment invariants for compatibility profiles

The compatibility predicates compare empirical symbol profiles inside coarse cells.  In the
Coppersmith--Winograd application, those profiles also remember a basic support invariant: a
symbol occurring in a logical-`Y` cell of value `j` has total weight `j`, and a symbol occurring
in a logical-`Z` cell of value `k` has total weight `k`.

This file isolates that invariant for an arbitrary feature alphabet.  Its main consequence is
the paper's containment statement: a label compatible with a coarse constituent has exactly the
coarse coordinate word of the corresponding leg.  In particular, compatibility may be combined
with hashing only after this invariant has been established; compatibility equations alone do
not imply that two labels share a hash index.
-/

namespace AlgebraicComplexity

open Tensor

namespace WordType

/-- A positive entry of a pushed-forward multiplicity profile has a positive raw preimage.
This is the support-level companion to `mappedType_comp`. -/
theorem exists_positive_of_mappedType_pos
    {Raw Feature : Type*} [Fintype Raw]
    (feature : Raw → Feature) (profile : Raw → ℕ) (symbol : Feature)
    (hpositive : 0 < mappedType feature profile symbol) :
    ∃ raw, feature raw = symbol ∧ 0 < profile raw := by
  classical
  unfold mappedType at hpositive
  rw [Finset.sum_pos_iff] at hpositive
  obtain ⟨raw, hraw, hprofile⟩ := hpositive
  exact ⟨raw, by simpa [letterFiber] using hraw, hprofile⟩

end WordType

namespace MoreAsymmetryCompatibility

universe u v w

namespace YCompatibilityCell

/-- Coarse logical-`Y` value represented by a `Y` compatibility cell. -/
def yValue {Part : Type u} : YCompatibilityCell Part → ℕ
  | .boundary q => q.1.y
  | .pooled _part y => y

@[simp] theorem yValue_yCompatibilityCell
    {Part : Type u} [DecidableEq Part] (q : CoarseIndex Part) :
    yValue (yCompatibilityCell q) = q.y := by
  unfold yCompatibilityCell
  split <;> rfl

end YCompatibilityCell

namespace ZCompatibilityCell

/-- Coarse logical-`Z` value represented by a `Z` compatibility cell. -/
def zValue {Part : Type u} : ZCompatibilityCell Part → ℕ
  | .boundary q => q.1.z
  | .pooled _part z => z

@[simp] theorem zValue_zCompatibilityCell
    {Part : Type u} [DecidableEq Part] (q : CoarseIndex Part) :
    zValue (zCompatibilityCell q) = q.z := by
  unfold zCompatibilityCell
  split <;> rfl

end ZCompatibilityCell

namespace FeatureCompatibilityTargets

variable {Part : Type u} {Symbol : Type w}

/-- Every symbol with positive prescribed `Y`-cell multiplicity has the cell's coarse
logical-`Y` value. -/
def IsYWeightSupported
    (targets : FeatureCompatibilityTargets Part Symbol)
    (symbolWeight : Symbol → ℕ) : Prop :=
  ∀ cell symbol, 0 < targets.yCellProfile cell symbol →
    symbolWeight symbol = cell.yValue

/-- Every symbol with positive prescribed `Z`-cell multiplicity has the cell's coarse
logical-`Z` value. -/
def IsZWeightSupported
    (targets : FeatureCompatibilityTargets Part Symbol)
    (symbolWeight : Symbol → ℕ) : Prop :=
  ∀ cell symbol, 0 < targets.zCellProfile cell symbol →
    symbolWeight symbol = cell.zValue

/-- The two containment-support invariants used by the `Y` and `Z` compatibility passes. -/
def IsWeightSupported
    (targets : FeatureCompatibilityTargets Part Symbol)
    (symbolWeight : Symbol → ℕ) : Prop :=
  targets.IsYWeightSupported symbolWeight ∧
    targets.IsZWeightSupported symbolWeight

end FeatureCompatibilityTargets

namespace CompatibilityTargets

variable {Part : Type u} {depth : ℕ}

/-- Raw `Y` support, expressed through the unified cell-profile interface. -/
theorem yCellProfile_weight_eq
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsYWeightSupported)
    (cell : YCompatibilityCell Part) (word : SplitWord depth)
    (hpositive : 0 < targets.yCellProfile cell word) :
    splitWordWeight word = cell.yValue := by
  cases cell with
  | boundary q => exact hsupported.1 q.1 word hpositive
  | pooled part total => exact hsupported.2 part total word hpositive

/-- Raw `Z` support, expressed through the unified cell-profile interface. -/
theorem zCellProfile_weight_eq
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsZWeightSupported)
    (cell : ZCompatibilityCell Part) (word : SplitWord depth)
    (hpositive : 0 < targets.zCellProfile cell word) :
    splitWordWeight word = cell.zValue := by
  cases cell with
  | boundary q => exact hsupported.1 q.1 word hpositive
  | pooled part total => exact hsupported.2 part total word hpositive

end CompatibilityTargets

namespace FeatureCompatibilityModel

variable {A : Leg → Type v} {Part : Type u} {Symbol : Type w}
variable {samples : ℕ}

/-- A compatible `Y` label has, sample by sample, the logical-`Y` coarse value of the
constituent with which it is compatible. -/
theorem symbolWeight_eq_coarseY_of_featureCompatibleY
    [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (symbolWeight : Symbol → ℕ)
    (hsupported : targets.IsYWeightSupported symbolWeight)
    (label : A .Y) (address : BlockAddress A)
    (hcompatible : model.FeatureCompatibleY targets label address)
    (sample : Fin samples) :
    symbolWeight (model.symbols .Y label sample) =
      (model.coarse address sample).y := by
  let cell := yCompatibilityCell (model.coarse address sample)
  let symbol := model.symbols .Y label sample
  have hpositive : 0 < cellMultiplicity
      (fun position ↦ yCompatibilityCell (model.coarse address position))
      (model.symbols .Y label) cell symbol :=
    cellMultiplicity_pos_of_apply_eq _ _ sample cell symbol rfl rfl
  have htargetPositive : 0 < targets.yCellProfile cell symbol := by
    rw [← hcompatible cell symbol]
    exact hpositive
  exact (hsupported cell symbol htargetPositive).trans
    (YCompatibilityCell.yValue_yCompatibilityCell _)

/-- A compatible `Z` label has, sample by sample, the logical-`Z` coarse value of the
constituent with which it is compatible. -/
theorem symbolWeight_eq_coarseZ_of_featureCompatibleZ
    [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (symbolWeight : Symbol → ℕ)
    (hsupported : targets.IsZWeightSupported symbolWeight)
    (label : A .Z) (address : BlockAddress A)
    (hcompatible : model.FeatureCompatibleZ targets label address)
    (sample : Fin samples) :
    symbolWeight (model.symbols .Z label sample) =
      (model.coarse address sample).z := by
  let cell := zCompatibilityCell (model.coarse address sample)
  let symbol := model.symbols .Z label sample
  have hpositive : 0 < cellMultiplicity
      (fun position ↦ zCompatibilityCell (model.coarse address position))
      (model.symbols .Z label) cell symbol :=
    cellMultiplicity_pos_of_apply_eq _ _ sample cell symbol rfl rfl
  have htargetPositive : 0 < targets.zCellProfile cell symbol := by
    rw [← hcompatible cell symbol]
    exact hpositive
  exact (hsupported cell symbol htargetPositive).trans
    (ZCompatibilityCell.zValue_zCompatibilityCell _)

end FeatureCompatibilityModel

end MoreAsymmetryCompatibility

end AlgebraicComplexity
