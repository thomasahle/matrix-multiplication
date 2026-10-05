/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightExtractionClients
import AlgebraicComplexity.Combinatorics.ProportionalTypeClassCore
import AlgebraicComplexity.MatrixMultiplication.RecursiveCompleteSplitOccurrenceLaw

/-!
# Total-weight profiles from labelled recursive occurrences

`RecursiveOccurrenceTargetData` records an exact split-word law on every labelled child
occurrence.  This module proves that selecting the corresponding full tagged coarse-cell type
supplies the reference equations required by the total-weight extraction clients.

The proof expands both finite pushforwards.  Coordinate support makes total weight deterministic
on each occurrence row, and `ComplementaryOccurrenceLaw.rowSum` then peels that row to its stated
occurrence mass.  Thus no search, generated table, entropy bound, or tensor restriction enters the
argument.
-/

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Repeat every row of a labelled occurrence law by the same integral factor. -/
def cwProportionalOccurrenceLaw
    {State : Type u} [Fintype State] {Symbol : Type v} [Fintype Symbol]
    {profile : State → ℕ} (law : ComplementaryOccurrenceLaw profile Symbol) (k : ℕ) :
    ComplementaryOccurrenceLaw (WordType.proportionalCounts profile k) Symbol where
  count occurrence symbol := law.count occurrence symbol * k
  rowSum occurrence := by
    calc
      (∑ symbol, law.count occurrence symbol * k) =
          (∑ symbol, law.count occurrence symbol) * k :=
        (Finset.sum_mul ..).symm
      _ = profile occurrence.orderedState * k := by rw [law.rowSum]
      _ = WordType.proportionalCounts profile k occurrence.orderedState := rfl

@[simp] theorem cwProportionalOccurrenceLaw_count
    {State : Type u} [Fintype State] {Symbol : Type v} [Fintype Symbol]
    {profile : State → ℕ} (law : ComplementaryOccurrenceLaw profile Symbol) (k : ℕ)
    (occurrence : ComplementaryOccurrence State) (symbol : Symbol) :
    (cwProportionalOccurrenceLaw law k).count occurrence symbol = law.count occurrence symbol * k :=
  rfl

variable {State : Type u} [Fintype State]
variable {Part : Type v} [DecidableEq Part]
variable {depth : ℕ} {profile : State → ℕ}

/-- Pooling a repeated occurrence law repeats every pooled entry by the same factor. -/
@[simp] theorem recursiveOccurrencePooledProfile_proportionalCounts
    {Cell : Type w} [DecidableEq Cell]
    (cellOf : ComplementaryOccurrence State → Cell)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
    (k : ℕ) (cell : Cell) (word : SplitWord depth) :
    recursiveOccurrencePooledProfile cellOf (cwProportionalOccurrenceLaw law k) cell word =
      recursiveOccurrencePooledProfile cellOf law cell word * k := by
  classical
  unfold recursiveOccurrencePooledProfile
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro occurrence _
  by_cases hcell : cellOf occurrence = cell <;> simp [hcell]

/-- Repeat all three labelled occurrence laws in one target package. -/
noncomputable def cwProportionalRecursiveOccurrenceTargetData
    {coarseOf : ComplementaryOccurrence State → CoarseIndex Part}
    (data : RecursiveOccurrenceTargetData (depth := depth) coarseOf profile) (k : ℕ) :
    RecursiveOccurrenceTargetData (depth := depth) coarseOf
      (WordType.proportionalCounts profile k) where
  law c := cwProportionalOccurrenceLaw (data.law c) k
  yBoundary q hq word := by
    simpa [recursiveOccurrenceExactProfile] using
      congrArg (fun value ↦ value * k) (data.yBoundary q hq word)
  zBoundaryOfX q hq word := by
    simpa [recursiveOccurrenceExactProfile] using
      congrArg (fun value ↦ value * k) (data.zBoundaryOfX q hq word)
  zBoundaryOfY q hq word := by
    simpa [recursiveOccurrenceExactProfile] using
      congrArg (fun value ↦ value * k) (data.zBoundaryOfY q hq word)

@[simp] theorem cwProportionalRecursiveOccurrenceTargetData_law
    {coarseOf : ComplementaryOccurrence State → CoarseIndex Part}
    (data : RecursiveOccurrenceTargetData (depth := depth) coarseOf profile)
    (k : ℕ) (c : Leg) :
    (cwProportionalRecursiveOccurrenceTargetData data k).law c =
      cwProportionalOccurrenceLaw (data.law c) k :=
  rfl

omit [DecidableEq Part] in
/-- A pooled occurrence profile inherits a coordinate-support law from its labelled rows. -/
private theorem recursiveOccurrencePooledProfile_weight_eq
    {Cell : Type w} [DecidableEq Cell]
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth)) (c : Leg)
    (hsupported : ∀ occurrence word, law.count occurrence word ≠ 0 →
      splitWordWeight word = (coarseOf occurrence).get c)
    (cellOf : ComplementaryOccurrence State → Cell) (cellValue : Cell → ℕ)
    (hcellValue : ∀ occurrence,
      cellValue (cellOf occurrence) = (coarseOf occurrence).get c)
    (cell : Cell) (word : SplitWord depth)
    (hpositive : 0 < recursiveOccurrencePooledProfile cellOf law cell word) :
    splitWordWeight word = cellValue cell := by
  classical
  unfold recursiveOccurrencePooledProfile at hpositive
  rw [Finset.sum_pos_iff] at hpositive
  obtain ⟨occurrence, _hoccurrence, hterm⟩ := hpositive
  by_cases hcell : cellOf occurrence = cell
  · have hcount : 0 < law.count occurrence word := by
      simpa [hcell] using hterm
    calc
      splitWordWeight word = (coarseOf occurrence).get c :=
        hsupported occurrence word (Nat.ne_of_gt hcount)
      _ = cellValue (cellOf occurrence) := (hcellValue occurrence).symm
      _ = cellValue cell := congrArg cellValue hcell
  · simp [hcell] at hterm

/-- Coordinate support of the three labelled laws proves all exact and pooled support invariants
of the induced compatibility target package. -/
theorem cwRecursiveOccurrenceTargetData_isWeightSupported
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (data : RecursiveOccurrenceTargetData (depth := depth) coarseOf profile)
    (hsupported : ∀ c occurrence word,
      (data.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (coarseOf occurrence).get c) :
    data.toCompatibilityTargets.IsWeightSupported := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro q word hpositive
    exact recursiveOccurrencePooledProfile_weight_eq coarseOf (data.law .X) .X
      (hsupported .X) coarseOf (fun cell ↦ cell.x) (fun _ ↦ rfl) q word hpositive
  · intro q word hpositive
    exact recursiveOccurrencePooledProfile_weight_eq coarseOf (data.law .Y) .Y
      (hsupported .Y) coarseOf (fun cell ↦ cell.y) (fun _ ↦ rfl) q word hpositive
  · intro part total word hpositive
    exact recursiveOccurrencePooledProfile_weight_eq coarseOf (data.law .Y) .Y
      (hsupported .Y) (yCompatibilityCell ∘ coarseOf) YCompatibilityCell.yValue
        (fun occurrence ↦ by simp [Function.comp_apply, CoarseIndex.get])
        (.pooled part total) word hpositive
  · intro q word hpositive
    exact recursiveOccurrencePooledProfile_weight_eq coarseOf (data.law .Z) .Z
      (hsupported .Z) coarseOf (fun cell ↦ cell.z) (fun _ ↦ rfl) q word hpositive
  · intro part total word hpositive
    exact recursiveOccurrencePooledProfile_weight_eq coarseOf (data.law .Z) .Z
      (hsupported .Z) (zCompatibilityCell ∘ coarseOf) ZCompatibilityCell.zValue
        (fun occurrence ↦ by simp [Function.comp_apply, CoarseIndex.get])
        (.pooled part total) word hpositive

/-- The bounded full coarse cell attached to one labelled recursive occurrence. -/
def cwRecursiveOccurrenceFiniteCell
    {State : Type u} {Part : Type v} (depth : ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (occurrence : ComplementaryOccurrence State) :
    CWOrientedCoarseCell Part depth :=
  (coarseOf occurrence |>.part, fun c ↦
    ⟨(coarseOf occurrence).get c, by
      have hsum := htotal occurrence
      simp only [coarseTotal] at hsum
      cases c <;> simp only [CoarseIndex.get] <;> omega⟩)

/-- Forgetting the finite bounds recovers the occurrence's original coarse index. -/
@[simp] theorem cwOrientedCoarseCellToIndex_cwRecursiveOccurrenceFiniteCell
    {State : Type u} {Part : Type v} (depth : ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (occurrence : ComplementaryOccurrence State) :
    cwOrientedCoarseCellToIndex
        (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal occurrence) =
      coarseOf occurrence := by
  apply CoarseIndex.ext <;> rfl

/-- Integral full tagged cell type induced by the two labelled occurrences of every state. -/
noncomputable def cwRecursiveOccurrenceFullCellType
    {State : Type u} [Fintype State] {Part : Type v} (depth : ℕ)
    (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth) :
    CWOrientedCoarseCell Part depth → ℕ :=
  WordType.mappedType
    (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal)
    (fun occurrence ↦ occurrence.integralMass profile)

/-- Repeating every occurrence multiplicity repeats the induced full coarse-cell type. -/
theorem cwRecursiveOccurrenceFullCellType_proportionalCounts
    {State : Type u} [Fintype State] {Part : Type v} (depth : ℕ)
    (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (k : ℕ) :
    cwRecursiveOccurrenceFullCellType depth
        (WordType.proportionalCounts profile k) coarseOf htotal =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) k := by
  classical
  unfold cwRecursiveOccurrenceFullCellType
  have hprofile :
      (fun occurrence : ComplementaryOccurrence State ↦
        occurrence.integralMass (WordType.proportionalCounts profile k)) =
        WordType.proportionalCounts
          (fun occurrence ↦ occurrence.integralMass profile) k := by
    funext occurrence
    rfl
  rw [hprofile]
  exact WordType.mappedType_proportionalCounts
      (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal)
      (fun occurrence ↦ occurrence.integralMass profile) k

/-- Pooling an occurrence law by a coarse cell and then by total weight is the same finite
pushforward as mapping its raw occurrence/split-word profile directly to `(cell, weight)`. -/
theorem recursiveOccurrencePushedProfile_eq_mappedRawProfile
    {State : Type u} [Fintype State]
    {Part : Type v} {Cell : Type w} [DecidableEq Cell]
    {depth : ℕ} {profile : State → ℕ}
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
    (cellOf : CoarseIndex Part → Cell) (cell : Cell)
    (symbol : CWCoarseDigit depth) :
    WordType.mappedType (cwSplitWordTotalDigit depth)
        (recursiveOccurrencePooledProfile (cellOf ∘ coarseOf) law cell) symbol =
      WordType.mappedType
        (fun entry : ComplementaryOccurrence State × SplitWord depth ↦
          (cellOf (coarseOf entry.1), cwSplitWordTotalDigit depth entry.2))
        law.rawProfile (cell, symbol) := by
  classical
  rw [WordType.mappedType_eq_sum_ite, WordType.mappedType_eq_sum_ite]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _
  unfold recursiveOccurrencePooledProfile
  by_cases hsymbol : cwSplitWordTotalDigit depth word = symbol
  · simp [hsymbol, ComplementaryOccurrenceLaw.rawProfile, Prod.ext_iff]
  · simp [hsymbol, Prod.ext_iff]

/-- Coordinate support collapses the total-weight pushforward of a law to its deterministic
occurrence cell and the occurrence row mass. -/
theorem recursiveOccurrence_mappedRawProfile_eq_fullCellFeatureType
    {State : Type u} [Fintype State]
    {Part : Type v} {Cell : Type w} [DecidableEq Cell]
    {depth : ℕ} {profile : State → ℕ}
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (c : Leg)
    (hsupported : ∀ occurrence word, law.count occurrence word ≠ 0 →
      splitWordWeight word = (coarseOf occurrence).get c)
    (cellOf : CoarseIndex Part → Cell) :
    WordType.mappedType
        (fun entry : ComplementaryOccurrence State × SplitWord depth ↦
          (cellOf (coarseOf entry.1), cwSplitWordTotalDigit depth entry.2))
        law.rawProfile =
      WordType.mappedType
        (fun occurrence ↦
          (cellOf (coarseOf occurrence),
            (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal occurrence).2 c))
        (fun occurrence ↦ occurrence.integralMass profile) := by
  classical
  funext target
  obtain ⟨targetCell, targetSymbol⟩ := target
  rw [WordType.mappedType_eq_sum_ite, WordType.mappedType_eq_sum_ite]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro occurrence _
  have hweight (word : SplitWord depth)
      (hcount : law.count occurrence word ≠ 0) :
      cwSplitWordTotalDigit depth word =
        (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal occurrence).2 c := by
    apply Fin.ext
    exact hsupported occurrence word hcount
  by_cases hcell : cellOf (coarseOf occurrence) = targetCell
  · by_cases hdigit :
        (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal occurrence).2 c = targetSymbol
    · have hrow :
          (∑ word, if cwSplitWordTotalDigit depth word = targetSymbol then
              law.count occurrence word else 0) =
            ∑ word, law.count occurrence word := by
        apply Finset.sum_congr rfl
        intro word _
        by_cases hcount : law.count occurrence word = 0
        · simp [hcount]
        · rw [if_pos ((hweight word hcount).trans hdigit)]
      simp only [ComplementaryOccurrenceLaw.rawProfile, Prod.mk.injEq, hcell,
        hdigit, true_and, if_true]
      rw [hrow, law.rowSum]
      simp [ComplementaryOccurrence.integralMass]
    · have hrow :
          (∑ word, if cwSplitWordTotalDigit depth word = targetSymbol then
              law.count occurrence word else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro word _
        by_cases hcount : law.count occurrence word = 0
        · simp [hcount]
        · have hne : cwSplitWordTotalDigit depth word ≠ targetSymbol := by
            intro heq
            exact hdigit ((hweight word hcount).symm.trans heq)
          simp [hne]
      simp only [ComplementaryOccurrenceLaw.rawProfile, Prod.mk.injEq, hcell,
        true_and, hdigit, and_false, if_false]
      rw [hrow]
  · simp [Prod.ext_iff, hcell]

/-- A reference word realizing the occurrence full-cell type has the same projected
cell/coordinate multiplicity as the deterministic occurrence profile. -/
theorem cwTotalWeightReferenceMultiplicity_eq_fullCellFeatureType
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {Cell : Type w} [DecidableEq Cell]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal)
    (cellOf : CoarseIndex Part → Cell) (c : Leg) (cell : Cell)
    (symbol : CWCoarseDigit depth) :
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    cellMultiplicity (fun sample ↦ cellOf (model.coarse reference sample))
        (model.symbols c (reference c)) cell symbol =
      WordType.mappedType
        (fun occurrence ↦
          (cellOf (coarseOf occurrence),
            (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal occurrence).2 c))
        (fun occurrence ↦ occurrence.integralMass profile) (cell, symbol) := by
  classical
  dsimp only
  let feature : CWOrientedCoarseCell Part depth → Cell × CWCoarseDigit depth :=
    fun finiteCell ↦
      (cellOf (cwOrientedCoarseCellToIndex finiteCell), finiteCell.2 c)
  have hjoint :
      cellMultiplicity
          (fun sample ↦ cellOf
            ((cwTotalWeightFeatureCompatibilityModel depth n partAt).coarse
              reference sample))
          ((cwTotalWeightFeatureCompatibilityModel depth n partAt).symbols c
            (reference c)) cell symbol =
        WordType.multiplicity
          (fun sample ↦
            (cellOf
                ((cwTotalWeightFeatureCompatibilityModel depth n partAt).coarse
                  reference sample),
              (cwTotalWeightFeatureCompatibilityModel depth n partAt).symbols c
                (reference c) sample))
          (cell, symbol) := by
    classical
    unfold cellMultiplicity WordType.multiplicity
    apply congrArg Finset.card
    ext sample
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  rw [hjoint]
  change WordType.multiplicity
      (feature ∘
        cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference)
      (cell, symbol) = _
  rw [WordType.multiplicity_comp_eq_mappedType, hreference]
  unfold cwRecursiveOccurrenceFullCellType
  rw [WordType.mappedType_comp]
  simp only [feature, Function.comp_def,
    cwOrientedCoarseCellToIndex_cwRecursiveOccurrenceFiniteCell]

/-- **Generic occurrence-to-reference bridge.**  A full-cell-type reference and the explicit
coordinate support of one occurrence law determine every total-weight projected cell profile. -/
theorem cwTotalWeightReferenceMultiplicity_eq_recursiveOccurrencePushedProfile
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {Cell : Type w} [DecidableEq Cell]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (c : Leg)
    (hsupported : ∀ occurrence word, law.count occurrence word ≠ 0 →
      splitWordWeight word = (coarseOf occurrence).get c)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal)
    (cellOf : CoarseIndex Part → Cell) (cell : Cell)
    (symbol : CWCoarseDigit depth) :
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    cellMultiplicity (fun sample ↦ cellOf (model.coarse reference sample))
        (model.symbols c (reference c)) cell symbol =
      WordType.mappedType (cwSplitWordTotalDigit depth)
        (recursiveOccurrencePooledProfile (cellOf ∘ coarseOf) law cell) symbol := by
  calc
    _ = WordType.mappedType
        (fun occurrence ↦
          (cellOf (coarseOf occurrence),
            (cwRecursiveOccurrenceFiniteCell depth coarseOf htotal occurrence).2 c))
        (fun occurrence ↦ occurrence.integralMass profile) (cell, symbol) :=
      cwTotalWeightReferenceMultiplicity_eq_fullCellFeatureType
        depth n partAt profile coarseOf htotal reference hreference
          cellOf c cell symbol
    _ = WordType.mappedType
        (fun entry : ComplementaryOccurrence State × SplitWord depth ↦
          (cellOf (coarseOf entry.1), cwSplitWordTotalDigit depth entry.2))
        law.rawProfile (cell, symbol) :=
      congrFun (recursiveOccurrence_mappedRawProfile_eq_fullCellFeatureType
        coarseOf law htotal c hsupported cellOf).symm (cell, symbol)
    _ = _ := (recursiveOccurrencePushedProfile_eq_mappedRawProfile
      coarseOf law cellOf cell symbol).symm

/-- Identity-cell occurrence pooling is the exact recursive occurrence profile. -/
private theorem recursiveOccurrencePooledProfile_id_comp
    {State : Type u} [Fintype State]
    {Part : Type v} [DecidableEq Part]
    {depth : ℕ} {profile : State → ℕ}
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
    (cell : CoarseIndex Part) :
    recursiveOccurrencePooledProfile ((fun q ↦ q) ∘ coarseOf) law cell =
      recursiveOccurrenceExactProfile coarseOf law cell := by
  rfl

/-- Pooling through the `Y` compatibility-cell map is the recursive `Y` pooled profile. -/
private theorem recursiveOccurrencePooledProfile_yCompatibilityCell_comp
    {State : Type u} [Fintype State]
    {Part : Type v} [DecidableEq Part]
    {depth : ℕ} {profile : State → ℕ}
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
    (part : Part) (y : ℕ) :
    recursiveOccurrencePooledProfile (yCompatibilityCell ∘ coarseOf) law
        (.pooled part y) =
      recursiveOccurrenceYPooledProfile coarseOf law part y := by
  rfl

/-- Pooling through the `Z` compatibility-cell map is the recursive `Z` pooled profile. -/
private theorem recursiveOccurrencePooledProfile_zCompatibilityCell_comp
    {State : Type u} [Fintype State]
    {Part : Type v} [DecidableEq Part]
    {depth : ℕ} {profile : State → ℕ}
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (law : ComplementaryOccurrenceLaw profile (SplitWord depth))
    (part : Part) (z : ℕ) :
    recursiveOccurrencePooledProfile (zCompatibilityCell ∘ coarseOf) law
        (.pooled part z) =
      recursiveOccurrenceZPooledProfile coarseOf law part z := by
  rfl

/-- Recursive occurrence targets satisfy the single reference-profile predicate used by the
fixed-full-cell total-weight extraction client. -/
theorem cwTotalWeightReferenceProfiles_of_recursiveOccurrenceTargetData
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (data : RecursiveOccurrenceTargetData (depth := depth) coarseOf profile)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (hsupported : ∀ c occurrence word,
      (data.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (coarseOf occurrence).get c)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) :
    CWTotalWeightReferenceProfiles depth n partAt
      data.toCompatibilityTargets reference := by
  refine
    { matchesX := ?_
      matchesY := ?_
      pooledY := ?_
      pooledZ := ?_ }
  · intro cell symbol
    simpa [cwTotalWeightPushforwardTargets, cwTotalWeightPushforwardProfile,
      RecursiveOccurrenceTargetData.toCompatibilityTargets,
      recursiveOccurrencePooledProfile_id_comp] using
        (cwTotalWeightReferenceMultiplicity_eq_recursiveOccurrencePushedProfile
          depth n partAt profile coarseOf (data.law .X) htotal .X
            (hsupported .X) reference hreference (fun q ↦ q) cell symbol)
  · intro cell symbol
    simpa [cwTotalWeightPushforwardTargets, cwTotalWeightPushforwardProfile,
      RecursiveOccurrenceTargetData.toCompatibilityTargets,
      recursiveOccurrencePooledProfile_id_comp] using
        (cwTotalWeightReferenceMultiplicity_eq_recursiveOccurrencePushedProfile
          depth n partAt profile coarseOf (data.law .Y) htotal .Y
            (hsupported .Y) reference hreference (fun q ↦ q) cell symbol)
  · intro part y symbol
    simpa [cwTotalWeightPushforwardTargets, cwTotalWeightPushforwardProfile,
      RecursiveOccurrenceTargetData.toCompatibilityTargets,
      recursiveOccurrencePooledProfile_yCompatibilityCell_comp] using
        (cwTotalWeightReferenceMultiplicity_eq_recursiveOccurrencePushedProfile
          depth n partAt profile coarseOf (data.law .Y) htotal .Y
            (hsupported .Y) reference hreference yCompatibilityCell
              (.pooled part y) symbol)
  · intro part z symbol
    simpa [cwTotalWeightPushforwardTargets, cwTotalWeightPushforwardProfile,
      RecursiveOccurrenceTargetData.toCompatibilityTargets,
      recursiveOccurrencePooledProfile_zCompatibilityCell_comp] using
        (cwTotalWeightReferenceMultiplicity_eq_recursiveOccurrencePushedProfile
          depth n partAt profile coarseOf (data.law .Z) htotal .Z
            (hsupported .Z) reference hreference zCompatibilityCell
              (.pooled part z) symbol)

/-- **k-proportional occurrence-to-reference bridge.**  Repeating an occurrence package and its
full tagged cell type by `k` produces the exact scaled targets at the selected reference. -/
theorem cwTotalWeightReferenceProfiles_of_recursiveOccurrenceTargetData_proportionalCounts
    {State : Type u} [Fintype State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (profile : State → ℕ)
    (coarseOf : ComplementaryOccurrence State → CoarseIndex Part)
    (data : RecursiveOccurrenceTargetData (depth := depth) coarseOf profile)
    (htotal : ∀ occurrence,
      (coarseOf occurrence).x + (coarseOf occurrence).y +
        (coarseOf occurrence).z = coarseTotal depth)
    (hsupported : ∀ c occurrence word,
      (data.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (coarseOf occurrence).get c)
    (k : ℕ)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      WordType.proportionalCounts
        (cwRecursiveOccurrenceFullCellType depth profile coarseOf htotal) k) :
    CWTotalWeightReferenceProfiles depth n partAt
      (cwProportionalRecursiveOccurrenceTargetData data k).toCompatibilityTargets reference := by
  apply cwTotalWeightReferenceProfiles_of_recursiveOccurrenceTargetData
    depth n partAt (WordType.proportionalCounts profile k) coarseOf
      (cwProportionalRecursiveOccurrenceTargetData data k) htotal
  · intro c occurrence word hcount
    apply hsupported c occurrence word
    intro hzero
    exact hcount (by simp [hzero])
  · exact hreference.trans
      (cwRecursiveOccurrenceFullCellType_proportionalCounts
        depth profile coarseOf htotal k).symm

end AlgebraicComplexity.Examples
