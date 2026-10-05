import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry
import MatrixMultiplication.DyadicEntropy
import MatrixMultiplication.Generated.SimplifiedVolumeData
import MatrixMultiplication.SimplifiedExponentRecurrenceForm
import MatrixMultiplication.SimplifiedVolumeReconstruction
import MatrixMultiplication.SignedDyadicLogForm

/-!
# Exact retained-exponent recurrence for the simplified level-four certificate

This file gives the primary sparse probability tables an executable mathematical meaning.  It
starts with the lowest recursive layer, where the recurrence is especially small: the top law is
pushed to level-three occurrence masses, then multiplied by the regional and ordered-split laws,
and every positive total-four split is interpreted as a rational CW `112` leaf.

All arithmetic before the final entropy evaluation is on natural numbers.  The common occurrence
denominator is `2^(20 + 12 + 12)`.  Missing sparse coordinates are definitionally zero.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedExponentRecurrence

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.Generated.SimplifiedVolume
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

/-! ## Sparse-table lookup -/

def zipLookup : List ℕ → List ℕ → ℕ → ℕ
  | index :: indices, value :: values, target =>
      if index = target then value else zipLookup indices values target
  | _, _, _ => 0

def sparseMassNumeratorAt (data : SparseMassChunk) (atom : ℕ) : ℕ :=
  zipLookup data.atomIndices.toList data.numerators.toList atom

def sparseMassEntries (data : SparseMassChunk) : List (ℕ × ℕ) :=
  data.atomIndices.toList.zip data.numerators.toList

def findSparseRow : List ℕ → List (Array ℕ) → List (Array ℕ) → ℕ →
    List (ℕ × ℕ)
  | row :: rows, support :: supports, numerator :: numerators, target =>
      if row = target then support.toList.zip numerator.toList
      else findSparseRow rows supports numerators target
  | _, _, _, _ => []

def sparseDyadicNumeratorAt (data : SparseDyadicChunk) (row symbol : ℕ) : ℕ :=
  let entries := findSparseRow data.rowIndices.toList data.supportRows.toList
    data.numeratorRows.toList row
  zipLookup entries.unzip.1 entries.unzip.2 symbol

def sparseScalarNumeratorAt (data : SparseScalarChunk) (index : ℕ) : ℕ :=
  zipLookup data.scalarIndices.toList data.numerators.toList index

def massNumeratorAt (chunks : Array SparseMassChunk) (atom : ℕ) : ℕ :=
  (chunks.toList.map fun chunk => sparseMassNumeratorAt chunk atom).sum

def massEntries (chunks : Array SparseMassChunk) : List (ℕ × ℕ) :=
  chunks.toList.flatMap sparseMassEntries

def dyadicNumeratorAt (chunks : Array SparseDyadicChunk) (row symbol : ℕ) : ℕ :=
  (chunks.toList.map fun chunk => sparseDyadicNumeratorAt chunk row symbol).sum

def scalarNumeratorAt (chunks : Array SparseScalarChunk) (index : ℕ) : ℕ :=
  (chunks.toList.map fun chunk => sparseScalarNumeratorAt chunk index).sum

/-! ## Top-law pushforward -/

def topZeroAtomCount : ℕ := 6 * 48
def topBranchPairCount : ℕ := levelFourPairCount

def topBranchAtomIndex (root region : Fin 6) (pair : Fin levelFourPairCount) : ℕ :=
  topZeroAtomCount + (root.val * 6 + region.val) * levelFourPairCount + pair.val

def topBranchNumerator (root region : Fin 6) (pair : Fin levelFourPairCount) : ℕ :=
  massNumeratorAt topChunks (topBranchAtomIndex root region pair)

/-- Incoming orientation carried by a positive level-three node. -/
def nodeIncomingRegion (node : Fin nodeCount) : Fin 6 :=
  ⟨node.val % 6, Nat.mod_lt _ (by decide)⟩

/-- Contribution of one sparse top atom to a fixed positive level-three node. -/
def topAtomPositiveMassThreeContribution (node : Fin nodeCount) (entry : ℕ × ℕ) : ℕ :=
  if entry.1 < topZeroAtomCount then 0
  else
    let payload := entry.1 - topZeroAtomCount
    let region := payload / levelFourPairCount % 6
    let pair : Fin levelFourPairCount :=
      ⟨payload % levelFourPairCount, Nat.mod_lt _ (by decide)⟩
    let children := levelFourPair pair
    if region = (nodeIncomingRegion node).val then
      (if children.1 = nodeShape node then entry.2 else 0) +
        (if children.2 = nodeShape node then entry.2 else 0)
    else 0

/-- Exact extensional pushforward of the sparse top law to the `126` positive level-three
node/orientation occurrences. -/
def positiveMassThreeTable : Array ℕ :=
  Array.ofFn fun node : Fin nodeCount =>
    ((massEntries topChunks).map (topAtomPositiveMassThreeContribution node)).sum

/-- Exact top-law occurrence mass of one positive level-three node.  An ordered pair contributes
once for each side equal to the node shape; in particular a diagonal pair contributes twice. -/
def positiveMassThreeNumerator (node : Fin nodeCount) : ℕ :=
  positiveMassThreeTable[node.val]?.getD 0

/-! ## Regional and split-law lookup -/

def regionalNumerator (node : Fin nodeCount) (region : Fin regionCount) : ℕ :=
  dyadicNumeratorAt pos3AChunks node.val region.val

def splitRowIndex (node : Fin nodeCount) (region : Fin regionCount) : ℕ :=
  node.val * regionCount + region.val

def splitNumerator (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) : ℕ :=
  dyadicNumeratorAt pos3AlphaChunks (splitRowIndex node region) slot.val

/-- Numerator at the slot complementary to `slot`.  The reconstructed split list is duplicate
free, so this sum has at most one nonzero summand. -/
def complementarySplitNumerator (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) : ℕ :=
  ∑ other : Fin splitSlotCount,
    if splitSlotValid node other ∧
        splitShape node other = (nodeShape node).complement (splitShape node slot)
    then splitNumerator node region other else 0

def orderedSplitNumerator (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) : ℕ :=
  splitNumerator node region slot + complementarySplitNumerator node region slot

def muFlatIndex (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) : ℕ :=
  (node.val * regionCount + region.val) * splitSlotCount + slot.val

def muNumerator (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) : ℕ :=
  scalarNumeratorAt muChunks (muFlatIndex node region slot)

def isPositiveLevelTwoSlot (node : Fin nodeCount) (slot : Fin splitSlotCount) : Bool :=
  decide (splitSlotValid node slot ∧ (splitShape node slot).IsPositive)

/-- The unique coordinate equal to two in a positive total-four split shape. -/
def levelTwoHeavyCoordinate (shape : Shape) : Fin 3 :=
  if shape.x = 2 then 0 else if shape.y = 2 then 1 else 2

/-- Exact numerator of a positive level-two occurrence at denominator `2^44`. -/
def levelTwoOccurrenceNumeratorWith (massThree : Fin nodeCount → ℕ)
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) : ℕ :=
  if isPositiveLevelTwoSlot node slot then
    massThree node * regionalNumerator node region * orderedSplitNumerator node region slot
  else 0

def levelTwoOccurrenceNumerator :=
  levelTwoOccurrenceNumeratorWith positiveMassThreeNumerator

/-! ## Exact leaf-rate semantics -/

def positiveEdgeEntropyNumerators (numerator : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => numerator
  | ⟨1, _⟩ => 2 ^ localBits - 2 * numerator
  | ⟨2, _⟩ => numerator

def positiveEdgeEntropyFromNumerator (numerator : ℕ) : ℝ :=
  entropyTerm localBits numerator +
    entropyTerm localBits (2 ^ localBits - 2 * numerator) +
    entropyTerm localBits numerator

def levelTwoEntryRate (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) (coordinate : Fin 3) : ℝ :=
  let occurrence := levelTwoOccurrenceNumerator node region slot
  let leafRate :=
    if coordinate = levelTwoHeavyCoordinate (splitShape node slot)
    then positiveEdgeEntropyFromNumerator (muNumerator node region slot)
    else 1
  mass levelTwoOccurrenceBits occurrence * leafRate

/-- Certificate-order enumeration of all potential level-two entries.  Inactive and nonpositive
slots have occurrence numerator zero and therefore contribute nothing. -/
def levelTwoIndices : List (Fin nodeCount × Fin regionCount × Fin splitSlotCount) :=
  (List.finRange nodeCount).flatMap fun node =>
    (List.finRange regionCount).flatMap fun region =>
      (List.finRange splitSlotCount).map fun slot => (node, region, slot)

/-- The three level-two retained-rate branches reconstructed from the exact sparse primary
tables. -/
def levelTwoBranchRate (coordinate : Fin 3) : ℝ :=
  (levelTwoIndices.map fun index =>
    levelTwoEntryRate index.1 index.2.1 index.2.2 coordinate).sum

/-- Actual branch minimum contributed by the positive level-two CW leaves. -/
def levelTwoRetainedExponent : ℝ :=
  min (levelTwoBranchRate 0) (min (levelTwoBranchRate 1) (levelTwoBranchRate 2))

/-! ## Exact log-linear expansion -/

def levelTwoEntryForm (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) (coordinate : Fin 3) : Form :=
  let occurrence := levelTwoOccurrenceNumerator node region slot
  if occurrence = 0 then Form.zero
  else if coordinate = levelTwoHeavyCoordinate (splitShape node slot) then
    positiveEdgeEntropyForm occurrence (muNumerator node region slot)
  else
    { constantNumerator := occurrence * 2 ^ localBits, terms := [] }

def levelTwoBranchForm (coordinate : Fin 3) : Form :=
  Form.sum (levelTwoIndices.map fun index =>
    levelTwoEntryForm index.1 index.2.1 index.2.2 coordinate)

theorem weightedEntropyTermForm_eval (occurrence numerator : ℕ) :
    Form.eval levelTwoFormBits (weightedEntropyTermForm occurrence numerator) =
      mass levelTwoOccurrenceBits occurrence * entropyTerm localBits numerator := by
  by_cases hn : numerator = 0
  · subst numerator
    simp [weightedEntropyTermForm, entropyTerm_zero]
  · have hpos : 0 < numerator := Nat.pos_of_ne_zero hn
    rw [entropyTerm_eq hpos]
    simp only [weightedEntropyTermForm, hn, if_false, Form.eval, Form.termsValue,
      Form.termValue, log2Nat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Int.cast_neg]
    norm_num [levelTwoFormBits, levelTwoOccurrenceBits, localBits, topBits, mass]
    ring

theorem positiveEdgeEntropyForm_eval (occurrence numerator : ℕ) :
    Form.eval levelTwoFormBits (positiveEdgeEntropyForm occurrence numerator) =
      mass levelTwoOccurrenceBits occurrence *
        positiveEdgeEntropyFromNumerator numerator := by
  rw [positiveEdgeEntropyForm, Form.eval_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    weightedEntropyTermForm_eval, positiveEdgeEntropyFromNumerator]
  ring

theorem levelTwoEntryForm_eval (node : Fin nodeCount) (region : Fin regionCount)
    (slot : Fin splitSlotCount) (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (levelTwoEntryForm node region slot coordinate) =
      levelTwoEntryRate node region slot coordinate := by
  unfold levelTwoEntryForm levelTwoEntryRate
  dsimp only
  by_cases hocc : levelTwoOccurrenceNumerator node region slot = 0
  · simp [hocc, mass]
  · simp only [hocc, if_false]
    by_cases hc : coordinate = levelTwoHeavyCoordinate (splitShape node slot)
    · simp [hc, positiveEdgeEntropyForm_eval]
    · simp only [hc, if_false, Form.eval, Form.termsValue, List.map_nil,
        List.sum_nil, add_zero]
      norm_num [levelTwoFormBits, levelTwoOccurrenceBits, localBits, topBits, mass]
      ring

theorem levelTwoBranchForm_eval (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (levelTwoBranchForm coordinate) =
      levelTwoBranchRate coordinate := by
  rw [levelTwoBranchForm, Form.eval_sum]
  unfold levelTwoBranchRate
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro index _
  exact levelTwoEntryForm_eval index.1 index.2.1 index.2.2 coordinate

/-! ## Chunked reconstruction through the shared primary-table recurrence

The definitions above are convenient mathematical presentations indexed by typed nodes, regions,
and slots.  Exact generated checking needs a more reduction-friendly presentation.  The scalar
volume reconstruction already supplies the same top-pair pushforward as a cached array and numbers
the `126 * 6 * 10` level-two edges consecutively.  The following definitions reuse that boundary,
but give each positive edge its retained-rate rather than its matrix-volume contribution.

The array `massThree` remains an explicit parameter.  Consequently a generated checker can first
seal the top-pair scatter once, rewrite it to a short literal array, and then check moderate edge
ranges without re-running the top scatter for every edge.
-/

namespace Chunked

def edgeCount : ℕ := MatrixMultiplication.SimplifiedVolumeReconstruction.edgeCount
def edgeChunkCount : ℕ :=
  MatrixMultiplication.SimplifiedVolumeReconstruction.edgeChunkCount
def edgeChunkSize : ℕ :=
  MatrixMultiplication.SimplifiedVolumeReconstruction.edgeChunkSize

/-- Three coordinate forms checked together so a generated chunk evaluates the primary lookup
only once. -/
structure BranchForms where
  branch0 : Form
  branch1 : Form
  branch2 : Form
  deriving DecidableEq, Repr

def edgeActive (edge : ℕ) : Bool :=
  let node := MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode edge
  let slot := MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot edge
  MatrixMultiplication.SimplifiedVolumeReconstruction.splitSlotIsValid node slot &&
    (MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt node slot).IsPositive

def edgeHeavyCoordinate (edge : ℕ) : Fin 3 :=
  levelTwoHeavyCoordinate
    (MatrixMultiplication.SimplifiedVolumeReconstruction.splitShapeAt
      (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeNode edge)
      (MatrixMultiplication.SimplifiedVolumeReconstruction.edgeSlot edge))

def edgeOccurrenceNumeratorWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (edge : ℕ) : ℕ :=
  if edgeActive edge then
    MatrixMultiplication.SimplifiedVolumeReconstruction.levelTwoMassNumeratorWithMass3
      data massThree edge
  else 0

def edgeMuNumerator
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (edge : ℕ) : ℕ :=
  MatrixMultiplication.SimplifiedVolumeReconstruction.scalarNumeratorAt data.mu edge

def edgeRateWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (edge : ℕ) (coordinate : Fin 3) : ℝ :=
  let occurrence := edgeOccurrenceNumeratorWithMassThree data massThree edge
  let leafRate :=
    if coordinate = edgeHeavyCoordinate edge then
      positiveEdgeEntropyFromNumerator (edgeMuNumerator data edge)
    else 1
  mass levelTwoOccurrenceBits occurrence * leafRate

def edgeFormWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (edge : ℕ) (coordinate : Fin 3) : Form :=
  let occurrence := edgeOccurrenceNumeratorWithMassThree data massThree edge
  if occurrence = 0 then Form.zero
  else if coordinate = edgeHeavyCoordinate edge then
    positiveEdgeEntropyForm occurrence (edgeMuNumerator data edge)
  else
    { constantNumerator := occurrence * 2 ^ localBits, terms := [] }

def edgeInputWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (edge : ℕ) : EdgeInput :=
  { occurrenceNumerator := edgeOccurrenceNumeratorWithMassThree data massThree edge
    muNumerator := edgeMuNumerator data edge
    heavyCoordinate := (edgeHeavyCoordinate edge).val }

def inputRate (input : EdgeInput) (coordinate : Fin 3) : ℝ :=
  let leafRate :=
    if coordinate.val = input.heavyCoordinate then
      positiveEdgeEntropyFromNumerator input.muNumerator
    else 1
  mass levelTwoOccurrenceBits input.occurrenceNumerator * leafRate

theorem inputForm_eval (input : EdgeInput) (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (inputForm input coordinate) = inputRate input coordinate := by
  unfold inputForm inputRate
  by_cases hocc : input.occurrenceNumerator = 0
  · simp [hocc, mass]
  · simp only [hocc, if_false]
    by_cases hc : coordinate.val = input.heavyCoordinate
    · simp [hc, positiveEdgeEntropyForm_eval]
    · simp only [hc, if_false, Form.eval, Form.termsValue, List.map_nil,
        List.sum_nil, add_zero]
      norm_num [levelTwoFormBits, levelTwoOccurrenceBits, localBits, topBits, mass]
      ring

/-- The geometrically positive level-two edges, in certificate order.  The result-specific
generated module checks its exact length and serialized values without burdening this generic
module's ordinary build. -/
def activeEdges : List ℕ :=
  (List.range edgeCount).filter edgeActive

def edgeInputRangeWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (edges : List ℕ) (start count : ℕ) : List EdgeInput :=
  ((edges.drop start).take count).map
    (edgeInputWithMassThree data massThree)

def activeEdgeInputRangeWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (start count : ℕ) : List EdgeInput :=
  edgeInputRangeWithMassThree data massThree activeEdges start count

def inputBranchRate (inputs : List EdgeInput) (coordinate : Fin 3) : ℝ :=
  (inputs.map fun input => inputRate input coordinate).sum

theorem inputBranchForm_eval (inputs : List EdgeInput) (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (inputBranchForm inputs coordinate) =
      inputBranchRate inputs coordinate := by
  rw [inputBranchForm, Form.eval_sum]
  unfold inputBranchRate
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro input _
  exact inputForm_eval input coordinate

def activeInputChunksWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) : List (List EdgeInput) :=
  [activeEdgeInputRangeWithMassThree data massThree 0 90,
    activeEdgeInputRangeWithMassThree data massThree 90 90,
    activeEdgeInputRangeWithMassThree data massThree 180 90,
    activeEdgeInputRangeWithMassThree data massThree 270 90,
    activeEdgeInputRangeWithMassThree data massThree 360 90,
    activeEdgeInputRangeWithMassThree data massThree 450 90,
    activeEdgeInputRangeWithMassThree data massThree 540 90,
    activeEdgeInputRangeWithMassThree data massThree 630 90,
    activeEdgeInputRangeWithMassThree data massThree 720 90,
    activeEdgeInputRangeWithMassThree data massThree 810 90,
    activeEdgeInputRangeWithMassThree data massThree 900 90,
    activeEdgeInputRangeWithMassThree data massThree 990 90,
    activeEdgeInputRangeWithMassThree data massThree 1080 90,
    activeEdgeInputRangeWithMassThree data massThree 1170 90,
    activeEdgeInputRangeWithMassThree data massThree 1260 90,
    activeEdgeInputRangeWithMassThree data massThree 1350 90,
    activeEdgeInputRangeWithMassThree data massThree 1440 90,
    activeEdgeInputRangeWithMassThree data massThree 1530 90]

def activeInputsWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) : List EdgeInput :=
  (activeInputChunksWithMassThree data massThree).flatten

def activeBranchFormWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (coordinate : Fin 3) : Form :=
  inputBranchForm (activeInputsWithMassThree data massThree) coordinate

def activeBranchRateWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (coordinate : Fin 3) : ℝ :=
  inputBranchRate (activeInputsWithMassThree data massThree) coordinate

theorem activeBranchFormWithMassThree_eval
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (activeBranchFormWithMassThree data massThree coordinate) =
      activeBranchRateWithMassThree data massThree coordinate := by
  exact inputBranchForm_eval _ _

def edgeRange (start count : ℕ) : List ℕ :=
  (List.range count).map (start + ·)

def branchRangeRateWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (coordinate : Fin 3) (start count : ℕ) : ℝ :=
  ((edgeRange start count).map fun edge =>
    edgeRateWithMassThree data massThree edge coordinate).sum

def branchRangeFormWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (coordinate : Fin 3) (start count : ℕ) : Form :=
  Form.sum ((edgeRange start count).map fun edge =>
    edgeFormWithMassThree data massThree edge coordinate)

def branchRangeFormsWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (start count : ℕ) : BranchForms :=
  { branch0 := branchRangeFormWithMassThree data massThree 0 start count
    branch1 := branchRangeFormWithMassThree data massThree 1 start count
    branch2 := branchRangeFormWithMassThree data massThree 2 start count }

theorem edgeFormWithMassThree_eval
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (edge : ℕ) (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (edgeFormWithMassThree data massThree edge coordinate) =
      edgeRateWithMassThree data massThree edge coordinate := by
  unfold edgeFormWithMassThree edgeRateWithMassThree
  dsimp only
  by_cases hocc : edgeOccurrenceNumeratorWithMassThree data massThree edge = 0
  · simp [hocc, mass]
  · simp only [hocc, if_false]
    by_cases hc : coordinate = edgeHeavyCoordinate edge
    · simp [hc, positiveEdgeEntropyForm_eval]
    · simp only [hc, if_false, Form.eval, Form.termsValue, List.map_nil,
        List.sum_nil, add_zero]
      norm_num [levelTwoFormBits, levelTwoOccurrenceBits, localBits, topBits, mass]
      ring

theorem branchRangeFormWithMassThree_eval
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ) (coordinate : Fin 3) (start count : ℕ) :
    Form.eval levelTwoFormBits
        (branchRangeFormWithMassThree data massThree coordinate start count) =
      branchRangeRateWithMassThree data massThree coordinate start count := by
  rw [branchRangeFormWithMassThree, Form.eval_sum]
  unfold branchRangeRateWithMassThree
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro edge _
  exact edgeFormWithMassThree_eval data massThree edge coordinate

def branchChunkFormsWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (coordinate : Fin 3) : List Form :=
  [branchRangeFormWithMassThree data massThree coordinate 0 540,
    branchRangeFormWithMassThree data massThree coordinate 540 540,
    branchRangeFormWithMassThree data massThree coordinate 1080 540,
    branchRangeFormWithMassThree data massThree coordinate 1620 540,
    branchRangeFormWithMassThree data massThree coordinate 2160 540,
    branchRangeFormWithMassThree data massThree coordinate 2700 540,
    branchRangeFormWithMassThree data massThree coordinate 3240 540,
    branchRangeFormWithMassThree data massThree coordinate 3780 540,
    branchRangeFormWithMassThree data massThree coordinate 4320 540,
    branchRangeFormWithMassThree data massThree coordinate 4860 540,
    branchRangeFormWithMassThree data massThree coordinate 5400 540,
    branchRangeFormWithMassThree data massThree coordinate 5940 540,
    branchRangeFormWithMassThree data massThree coordinate 6480 540,
    branchRangeFormWithMassThree data massThree coordinate 7020 540]

def branchChunkRatesWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (coordinate : Fin 3) : List ℝ :=
  [branchRangeRateWithMassThree data massThree coordinate 0 540,
    branchRangeRateWithMassThree data massThree coordinate 540 540,
    branchRangeRateWithMassThree data massThree coordinate 1080 540,
    branchRangeRateWithMassThree data massThree coordinate 1620 540,
    branchRangeRateWithMassThree data massThree coordinate 2160 540,
    branchRangeRateWithMassThree data massThree coordinate 2700 540,
    branchRangeRateWithMassThree data massThree coordinate 3240 540,
    branchRangeRateWithMassThree data massThree coordinate 3780 540,
    branchRangeRateWithMassThree data massThree coordinate 4320 540,
    branchRangeRateWithMassThree data massThree coordinate 4860 540,
    branchRangeRateWithMassThree data massThree coordinate 5400 540,
    branchRangeRateWithMassThree data massThree coordinate 5940 540,
    branchRangeRateWithMassThree data massThree coordinate 6480 540,
    branchRangeRateWithMassThree data massThree coordinate 7020 540]

def branchFormWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (coordinate : Fin 3) : Form :=
  Form.sum (branchChunkFormsWithMassThree data massThree coordinate)

def branchRateWithMassThree
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (coordinate : Fin 3) : ℝ :=
  (branchChunkRatesWithMassThree data massThree coordinate).sum

theorem branchFormWithMassThree_eval
    (data : MatrixMultiplication.SimplifiedVolumeReconstruction.PrimaryTables)
    (massThree : Array ℕ)
    (coordinate : Fin 3) :
    Form.eval levelTwoFormBits (branchFormWithMassThree data massThree coordinate) =
      branchRateWithMassThree data massThree coordinate := by
  rw [branchFormWithMassThree, Form.eval_sum]
  unfold branchChunkFormsWithMassThree branchRateWithMassThree branchChunkRatesWithMassThree
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [branchRangeFormWithMassThree_eval, branchRangeFormWithMassThree_eval,
    branchRangeFormWithMassThree_eval, branchRangeFormWithMassThree_eval,
    branchRangeFormWithMassThree_eval, branchRangeFormWithMassThree_eval,
    branchRangeFormWithMassThree_eval, branchRangeFormWithMassThree_eval,
    branchRangeFormWithMassThree_eval, branchRangeFormWithMassThree_eval,
    branchRangeFormWithMassThree_eval, branchRangeFormWithMassThree_eval,
    branchRangeFormWithMassThree_eval, branchRangeFormWithMassThree_eval]

/-- The exact level-two branch reconstructed from the generated sparse primary tables. -/
def reconstructedBranchRate (coordinate : Fin 3) : ℝ :=
  activeBranchRateWithMassThree
    MatrixMultiplication.SimplifiedVolumeReconstruction.generatedPrimaryTables
    (MatrixMultiplication.SimplifiedVolumeReconstruction.levelThreeMassNumerators
      MatrixMultiplication.SimplifiedVolumeReconstruction.generatedPrimaryTables)
    coordinate

/-- The exact minimum of the three reconstructed positive level-two branches. -/
def reconstructedRetainedExponent : ℝ :=
  min (reconstructedBranchRate 0)
    (min (reconstructedBranchRate 1) (reconstructedBranchRate 2))

end Chunked

end

end MatrixMultiplication.SimplifiedExponentRecurrence
