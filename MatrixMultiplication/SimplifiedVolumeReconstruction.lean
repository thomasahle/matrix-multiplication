import AlgebraicComplexity.MatrixMultiplication.LevelFourPairGeometry
import MatrixMultiplication.DyadicMassEntropy
import MatrixMultiplication.Generated.SimplifiedVolumeData
import MatrixMultiplication.Generated.SimplifiedVolumeScalarData
import MatrixMultiplication.LevelFourRemainingReconstruction
import Mathlib.Tactic.Ring

/-!
# Semantic reconstruction of the simplified rectangular-volume certificate

This module is the non-generated bridge between the exact sparse primary tables and the compact
log-linear volume certificate.  It has three deliberately separate layers:

* executable lookup functions interpret the generated sparse ambient indices;
* `scalarRecurrenceForm` performs the orientation-free level-four volume recurrence with exact
  natural-number arithmetic;
* `LogLinearForm.eval` gives that recurrence its real `log₂` semantics.

The generated checker proves that normalizing `scalarRecurrenceForm` gives `scalarExpectedForm`.
The analytic lemmas below prove that normalization does not change the value and that each leaf
formula is exactly the usual dyadic entropy/matrix-size contribution.  Thus the large generated
proof checks integers only; logarithms enter only through small reusable theorems.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedVolumeReconstruction

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.Generated.SimplifiedVolume

noncomputable section

/-! ## Sparse generated-data access -/

/-- Lookup in two parallel serialized lists.  Missing coordinates have numerator zero. -/
def zipLookup : List ℕ → List ℕ → ℕ → ℕ
  | index :: indices, value :: values, target =>
      if index = target then value else zipLookup indices values target
  | _, _, _ => 0

/-- Recover all `(ambient symbol, positive numerator)` entries of one ambient row. -/
def findSparseRow : List ℕ → List (Array ℕ) → List (Array ℕ) → ℕ →
    List (ℕ × ℕ)
  | row :: rows, support :: supports, numerator :: numerators, target =>
      if row = target then support.toList.zip numerator.toList
      else findSparseRow rows supports numerators target
  | _, _, _, _ => []

def sparseMassEntries (data : SparseMassChunk) : List (ℕ × ℕ) :=
  data.atomIndices.toList.zip data.numerators.toList

def sparseMassNumeratorAt (data : SparseMassChunk) (atom : ℕ) : ℕ :=
  zipLookup data.atomIndices.toList data.numerators.toList atom

def sparseDyadicRowEntries (data : SparseDyadicChunk) (row : ℕ) : List (ℕ × ℕ) :=
  findSparseRow data.rowIndices.toList data.supportRows.toList data.numeratorRows.toList row

def sparseDyadicNumeratorAt (data : SparseDyadicChunk) (row symbol : ℕ) : ℕ :=
  zipLookup (sparseDyadicRowEntries data row).unzip.1
    (sparseDyadicRowEntries data row).unzip.2 symbol

def sparseScalarNumeratorAt (data : SparseScalarChunk) (index : ℕ) : ℕ :=
  zipLookup data.scalarIndices.toList data.numerators.toList index

def massEntries (chunks : Array SparseMassChunk) : List (ℕ × ℕ) :=
  chunks.toList.flatMap sparseMassEntries

def massNumeratorAt (chunks : Array SparseMassChunk) (atom : ℕ) : ℕ :=
  (chunks.toList.map fun chunk => sparseMassNumeratorAt chunk atom).sum

def dyadicRowEntries (chunks : Array SparseDyadicChunk) (row : ℕ) : List (ℕ × ℕ) :=
  chunks.toList.flatMap fun chunk => sparseDyadicRowEntries chunk row

def dyadicNumeratorAt (chunks : Array SparseDyadicChunk) (row symbol : ℕ) : ℕ :=
  (chunks.toList.map fun chunk => sparseDyadicNumeratorAt chunk row symbol).sum

def scalarNumeratorAt (chunks : Array SparseScalarChunk) (index : ℕ) : ℕ :=
  (chunks.toList.map fun chunk => sparseScalarNumeratorAt chunk index).sum

/-! ## Exact log-linear forms -/

def log2Nat (argument : ℕ) : ℝ :=
  Real.log (argument : ℝ) / Real.log 2

structure LogTerm where
  argument : ℕ
  coefficient : ℤ
  deriving DecidableEq, Repr

structure LogLinearForm where
  constantNumerator : ℕ
  terms : List LogTerm
  deriving DecidableEq, Repr

namespace LogLinearForm

def zero : LogLinearForm := ⟨0, []⟩

def add (left right : LogLinearForm) : LogLinearForm :=
  ⟨left.constantNumerator + right.constantNumerator, left.terms ++ right.terms⟩

def sum (forms : List LogLinearForm) : LogLinearForm :=
  ⟨(forms.map constantNumerator).sum, forms.flatMap terms⟩

def termValue (bits : ℕ) (term : LogTerm) : ℝ :=
  (term.coefficient : ℝ) / (2 : ℝ) ^ bits * log2Nat term.argument

def termsValue (bits : ℕ) (terms : List LogTerm) : ℝ :=
  (terms.map (termValue bits)).sum

@[simp] theorem termsValue_append (bits : ℕ) (left right : List LogTerm) :
    termsValue bits (left ++ right) = termsValue bits left + termsValue bits right := by
  simp [termsValue]

def eval (bits : ℕ) (form : LogLinearForm) : ℝ :=
  mass bits form.constantNumerator + termsValue bits form.terms

/-- Insert one term into an argument-sorted list, combining equal arguments and deleting zero
coefficients. -/
def insert (term : LogTerm) : List LogTerm → List LogTerm
  | [] => if term.coefficient = 0 then [] else [term]
  | head :: tail =>
      if term.coefficient = 0 then head :: tail
      else if term.argument < head.argument then term :: head :: tail
      else if term.argument = head.argument then
        let coefficient := term.coefficient + head.coefficient
        if coefficient = 0 then tail else ⟨term.argument, coefficient⟩ :: tail
      else head :: insert term tail

def normalizeTerms (terms : List LogTerm) : List LogTerm :=
  terms.foldr insert []

def normalize (form : LogLinearForm) : LogLinearForm :=
  ⟨form.constantNumerator, normalizeTerms form.terms⟩

theorem termValue_zero_coefficient (bits argument : ℕ) :
    termValue bits ⟨argument, 0⟩ = 0 := by
  simp [termValue]

theorem termValue_add_coefficient (bits argument : ℕ) (left right : ℤ) :
    termValue bits ⟨argument, left + right⟩ =
      termValue bits ⟨argument, left⟩ + termValue bits ⟨argument, right⟩ := by
  simp only [termValue, Int.cast_add]
  ring

theorem termsValue_insert (bits : ℕ) (term : LogTerm) (terms : List LogTerm) :
    termsValue bits (insert term terms) = termValue bits term + termsValue bits terms := by
  rcases term with ⟨termArgument, termCoefficient⟩
  induction terms with
  | nil =>
      by_cases hzero : termCoefficient = 0
      · simp [insert, hzero, termsValue, termValue]
      · simp [insert, hzero, termsValue]
  | cons head tail ih =>
      rcases head with ⟨headArgument, headCoefficient⟩
      by_cases hzero : termCoefficient = 0
      · simp [insert, hzero, termsValue, termValue]
      · by_cases hlt : termArgument < headArgument
        · simp [insert, hzero, hlt, termsValue]
        · by_cases heq : termArgument = headArgument
          · subst headArgument
            by_cases hsum : termCoefficient + headCoefficient = 0
            · have hcancel :
                termValue bits ⟨termArgument, termCoefficient⟩ +
                      termValue bits ⟨termArgument, headCoefficient⟩ = 0 := by
                  rw [← termValue_add_coefficient]
                  rw [hsum, termValue_zero_coefficient]
              simp only [insert, hzero, hlt, if_false, if_true, hsum,
                termsValue, List.map_cons, List.sum_cons]
              change
                (List.map (termValue bits) tail).sum =
                  termValue bits ⟨termArgument, termCoefficient⟩ +
                    (termValue bits ⟨termArgument, headCoefficient⟩ +
                      (List.map (termValue bits) tail).sum)
              rw [← add_assoc, hcancel, zero_add]
            · simp only [insert, hzero, hlt, hsum, if_false, if_true,
                termsValue, List.map_cons, List.sum_cons]
              rw [termValue_add_coefficient]
              ring
          · simp only [insert, hzero, hlt, heq, if_false, termsValue,
              List.map_cons, List.sum_cons]
            change
              (List.map (termValue bits)
                (insert ⟨termArgument, termCoefficient⟩ tail)).sum =
                termValue bits ⟨termArgument, termCoefficient⟩ +
                  (List.map (termValue bits) tail).sum at ih
            rw [ih]
            ring

theorem termsValue_normalizeTerms (bits : ℕ) (terms : List LogTerm) :
    termsValue bits (normalizeTerms terms) = termsValue bits terms := by
  induction terms with
  | nil => rfl
  | cons head tail ih =>
      change termsValue bits (insert head (List.foldr insert [] tail)) = _
      rw [termsValue_insert]
      change termsValue bits (List.foldr insert [] tail) = termsValue bits tail at ih
      rw [ih]
      rfl

theorem eval_normalize (bits : ℕ) (form : LogLinearForm) :
    eval bits (normalize form) = eval bits form := by
  simp [eval, normalize, termsValue_normalizeTerms]

theorem mass_add (bits left right : ℕ) :
    mass bits (left + right) = mass bits left + mass bits right := by
  unfold mass
  push_cast
  ring

/-- Evaluation is additive over a finite list of exact forms. -/
theorem eval_sum (bits : ℕ) (forms : List LogLinearForm) :
    eval bits (sum forms) = (forms.map (eval bits)).sum := by
  induction forms with
  | nil => simp [sum, eval, termsValue, mass]
  | cons head tail ih =>
      simp only [sum, List.map_cons, List.sum_cons, List.flatMap_cons, eval,
        termsValue_append, mass_add]
      change
        mass bits ((tail.map constantNumerator).sum) +
            termsValue bits (tail.flatMap terms) =
          (tail.map (eval bits)).sum at ih
      linear_combination ih

theorem eval_eq_of_normalize_eq {left right : LogLinearForm}
    (h : normalize left = normalize right) (bits : ℕ) :
    eval bits left = eval bits right := by
  calc
    eval bits left = eval bits (normalize left) := (eval_normalize bits left).symm
    _ = eval bits (normalize right) := congrArg (eval bits) h
    _ = eval bits right := eval_normalize bits right

end LogLinearForm

/-! ## Leaf semantics and exact coefficient expansion -/

def zeroLeafValue {I : Type*} [Fintype I]
    (bits : ℕ) (numerator ones : I → ℕ) : ℝ :=
  (∑ i, entropyTerm bits (numerator i)) +
    mass bits (∑ i, numerator i * ones i) * log2Nat 5

def weightedZeroLeafValue {I : Type*} [Fintype I]
    (outerBits localBits outerNumerator : ℕ)
    (numerator ones : I → ℕ) : ℝ :=
  mass outerBits outerNumerator * zeroLeafValue localBits numerator ones

theorem mass_mul_mass (leftBits rightBits left right : ℕ) :
    mass leftBits left * mass rightBits right =
      mass (leftBits + rightBits) (left * right) := by
  simp only [mass]
  rw [pow_add]
  push_cast
  field_simp

theorem mass_rescale_right (bits extra numerator : ℕ) :
    mass bits numerator = mass (bits + extra) (numerator * 2 ^ extra) := by
  simpa [AlgebraicComplexity.dyadicDenominator] using
    (MatrixMultiplication.DyadicMassEntropy.mass_rescale bits extra numerator).symm

theorem mass_mul_mass_rescale
    (leftBits rightBits extra left right : ℕ) :
    mass leftBits left * mass rightBits right =
      mass (leftBits + rightBits + extra) (left * right * 2 ^ extra) := by
  rw [mass_mul_mass, mass_rescale_right]

theorem sum_mass {I : Type*} [Fintype I]
    (bits : ℕ) (numerator : I → ℕ) :
    (∑ i, mass bits (numerator i)) = mass bits (∑ i, numerator i) := by
  unfold mass
  rw [← Finset.sum_div]
  push_cast
  rfl

/-- A normalized positive dyadic zero-law row expands exactly to the integer coefficients used by
the generated checker. -/
theorem weightedZeroLeafValue_eq {I : Type*} [Fintype I]
    (outerBits localBits extra outerNumerator : ℕ)
    (numerator ones : I → ℕ)
    (hpos : ∀ i, 0 < numerator i)
    (hnormalized : (∑ i, numerator i) = 2 ^ localBits) :
    weightedZeroLeafValue outerBits localBits outerNumerator numerator ones =
      mass (outerBits + localBits + extra)
          (outerNumerator * localBits * 2 ^ localBits * 2 ^ extra) +
        mass (outerBits + localBits + extra)
            (outerNumerator * (∑ i, numerator i * ones i) * 2 ^ extra) * log2Nat 5 -
        ∑ i, mass (outerBits + localBits + extra)
            (outerNumerator * numerator i * 2 ^ extra) * log2Nat (numerator i) := by
  unfold weightedZeroLeafValue zeroLeafValue
  rw [mul_add, Finset.mul_sum]
  simp_rw [entropyTerm_eq (hpos _)]
  simp_rw [mul_sub]
  simp_rw [← mul_assoc]
  simp_rw [mass_mul_mass_rescale outerBits localBits extra]
  rw [Finset.sum_sub_distrib]
  have hconstant :
      (∑ i, mass (outerBits + localBits + extra)
          (outerNumerator * numerator i * 2 ^ extra) * (localBits : ℝ)) =
        mass (outerBits + localBits + extra)
          (outerNumerator * localBits * 2 ^ localBits * 2 ^ extra) := by
    have hnat :
        (∑ i, outerNumerator * numerator i * 2 ^ extra) =
          outerNumerator * 2 ^ localBits * 2 ^ extra := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hnormalized]
    rw [← Finset.sum_mul, sum_mass, hnat]
    unfold mass
    push_cast
    ring
  rw [hconstant]
  unfold log2Nat
  ring

def weightedPositiveEdgeValue
    (outerBits localBits outerNumerator muNumerator : ℕ) : ℝ :=
  mass outerBits outerNumerator *
    (2 - 2 * mass localBits muNumerator) * log2Nat 5

/-- A positive edge is one positive `log₂ 5` coefficient at the combined denominator. -/
theorem weightedPositiveEdgeValue_eq
    (outerBits localBits outerNumerator muNumerator : ℕ)
    (hmu : 2 * muNumerator ≤ 2 * 2 ^ localBits) :
    weightedPositiveEdgeValue outerBits localBits outerNumerator muNumerator =
      mass (outerBits + localBits)
          (outerNumerator * (2 * 2 ^ localBits - 2 * muNumerator)) * log2Nat 5 := by
  unfold weightedPositiveEdgeValue log2Nat mass
  rw [pow_add]
  push_cast
  rw [Nat.cast_sub hmu]
  push_cast
  field_simp

/-! ## Static recurrence geometry -/

def topBits : ℕ := 20
def localBits : ℕ := 12
def commonBits : ℕ := 56
def localDenominator : ℕ := 2 ^ localBits

def topZeroAtomCount : ℕ := 6 * 48
def topPairCount : ℕ := 1785
def edgeCount : ℕ := 126 * 6 * 10
def zeroThreeCount : ℕ := 45 * 6
def zeroFourCount : ℕ := 6 * 48

/-- The seven exact primary families consumed by the volume recurrence. -/
structure PrimaryTables where
  top : Array SparseMassChunk
  pos3A : Array SparseDyadicChunk
  pos3Alpha : Array SparseDyadicChunk
  edgeZero2 : Array SparseDyadicChunk
  zero3 : Array SparseDyadicChunk
  zero4 : Array SparseDyadicChunk
  mu : Array SparseScalarChunk

def generatedPrimaryTables : PrimaryTables where
  top := topChunks
  pos3A := pos3AChunks
  pos3Alpha := pos3AlphaChunks
  edgeZero2 := edgeZero2Chunks
  zero3 := zero3Chunks
  zero4 := zero4Chunks
  mu := muChunks

def shapeEightIndex (shape : Shape) : ℕ :=
  (shapes 8).idxOf shape

def computedPairShapeIndexRange (start count : ℕ) : List (ℕ × ℕ) :=
  ((levelFourPairs.drop start).take count).map fun pair =>
    (shapeEightIndex pair.1, shapeEightIndex pair.2)

def computedPairShapeIndices : Array (ℕ × ℕ) :=
  (computedPairShapeIndexRange 0 119 ++
    computedPairShapeIndexRange 119 119 ++
    computedPairShapeIndexRange 238 119 ++
    computedPairShapeIndexRange 357 119 ++
    computedPairShapeIndexRange 476 119 ++
    computedPairShapeIndexRange 595 119 ++
    computedPairShapeIndexRange 714 119 ++
    computedPairShapeIndexRange 833 119 ++
    computedPairShapeIndexRange 952 119 ++
    computedPairShapeIndexRange 1071 119 ++
    computedPairShapeIndexRange 1190 119 ++
    computedPairShapeIndexRange 1309 119 ++
    computedPairShapeIndexRange 1428 119 ++
    computedPairShapeIndexRange 1547 119 ++
    computedPairShapeIndexRange 1666 119).toArray

def topBranchChildIndexWithPairs
    (pairShapeIndices : Array (ℕ × ℕ)) (right : Bool) (flat : ℕ) : ℕ :=
  let pair := pairShapeIndices[flat % topPairCount]?.getD default
  let shapeIndex := if right then pair.2 else pair.1
  shapeIndex * 6 + (flat / topPairCount) % 6

def topEntryLevelThreeContributionWithPairs
    (pairShapeIndices : Array (ℕ × ℕ)) (row : ℕ) (entry : ℕ × ℕ) : ℕ :=
  if topZeroAtomCount ≤ entry.1 then
    let flat := entry.1 - topZeroAtomCount
    entry.2 *
      ((if topBranchChildIndexWithPairs pairShapeIndices false flat = row then 1 else 0) +
        if topBranchChildIndexWithPairs pairShapeIndices true flat = row then 1 else 0)
  else 0

def natInterval (start count : ℕ) : List ℕ :=
  (List.range count).map (start + ·)

/-- One level-three occurrence mass, reconstructed by scattering each selected top pair to its
two children. -/
def levelThreeMassNumeratorRawWithPairs
    (data : PrimaryTables) (pairShapeIndices : Array (ℕ × ℕ)) (row : ℕ) : ℕ :=
  ((massEntries data.top).map
    (topEntryLevelThreeContributionWithPairs pairShapeIndices row)).sum

/-- A selected positive top atom, with the two level-three rows to which its mass contributes. -/
structure TopScatterEntry where
  left : ℕ
  right : ℕ
  numerator : ℕ
  deriving DecidableEq, Repr

/-- Decode one sparse top entry into its two level-three child rows.  Zero-part atoms contribute
to the level-four zero leaves instead and are omitted here. -/
def topScatterEntryWithPairs
    (pairShapeIndices : Array (ℕ × ℕ)) (entry : ℕ × ℕ) : Option TopScatterEntry :=
  if topZeroAtomCount ≤ entry.1 then
    let flat := entry.1 - topZeroAtomCount
    some ⟨topBranchChildIndexWithPairs pairShapeIndices false flat,
      topBranchChildIndexWithPairs pairShapeIndices true flat, entry.2⟩
  else none

def topScatteredEntryRangeWithPairs
    (data : PrimaryTables) (pairShapeIndices : Array (ℕ × ℕ))
    (start count : ℕ) : List TopScatterEntry :=
  (((massEntries data.top).drop start).take count).filterMap
    (topScatterEntryWithPairs pairShapeIndices)

/-- All 2,308 active sparse top entries, decoded in bounded ranges.  The fixed range split is only
an evaluation boundary: concatenating `drop`/`take` windows preserves the serialized order. -/
def topScatteredEntriesWithPairs
    (data : PrimaryTables) (pairShapeIndices : Array (ℕ × ℕ)) : List TopScatterEntry :=
  topScatteredEntryRangeWithPairs data pairShapeIndices 0 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 128 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 256 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 384 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 512 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 640 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 768 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 896 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1024 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1152 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1280 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1408 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1536 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1664 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1792 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 1920 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 2048 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 2176 128 ++
    topScatteredEntryRangeWithPairs data pairShapeIndices 2304 4

/-- Add a mass to a global child row when that row lies in `[start, start + count)`. -/
def addMassInRange (start count : ℕ) (masses : Array ℕ) (row amount : ℕ) : Array ℕ :=
  if start ≤ row ∧ row < start + count then masses.modify (row - start) (· + amount)
  else masses

/-- Add one decoded top atom to each of its two level-three child rows inside a requested row
range.  The two additions are intentionally sequential: when both children agree, that row
receives the mass twice, exactly as in `topEntryLevelThreeContributionWithPairs`. -/
def scatterDecodedTopEntryRange
    (start count : ℕ) (masses : Array ℕ) (entry : TopScatterEntry) : Array ℕ :=
  addMassInRange start count
    (addMassInRange start count masses entry.left entry.numerator)
    entry.right entry.numerator

def levelThreeMassNumeratorRangeWithPairs
    (data : PrimaryTables) (pairShapeIndices : Array (ℕ × ℕ))
    (start count : ℕ) : List ℕ :=
  ((topScatteredEntriesWithPairs data pairShapeIndices).foldl
      (scatterDecodedTopEntryRange start count)
      (Array.replicate count 0)).toList

/-- Cached table of all 270 occurrence masses.  Keeping the scatter pass at this boundary avoids
repeating it for every one of the 7,560 level-two edges. -/
def levelThreeMassNumeratorsWithPairs
    (data : PrimaryTables) (pairShapeIndices : Array (ℕ × ℕ)) : Array ℕ :=
  (levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 0 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 30 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 60 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 90 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 120 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 150 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 180 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 210 30 ++
    levelThreeMassNumeratorRangeWithPairs data pairShapeIndices 240 30).toArray

def levelThreeMassNumerators (data : PrimaryTables) : Array ℕ :=
  levelThreeMassNumeratorsWithPairs data computedPairShapeIndices

theorem levelThreeMassNumerators_eq_withPairs (data : PrimaryTables) :
    levelThreeMassNumerators data =
      levelThreeMassNumeratorsWithPairs data computedPairShapeIndices := by
  rfl

def levelThreeMassNumerator (data : PrimaryTables) (row : ℕ) : ℕ :=
  (levelThreeMassNumerators data)[row]?.getD 0

def nodeShapeAt (node : ℕ) : Shape :=
  (positiveShapes 8)[node / 6]?.getD default

def splitShapeAt (node slot : ℕ) : Shape :=
  (levelThreeSplits (nodeShapeAt node))[slot]?.getD default

def splitSlotIsValid (node slot : ℕ) : Bool :=
  decide (slot < (levelThreeSplits (nodeShapeAt node)).length)

def complementSlotAt (node slot : ℕ) : ℕ :=
  (levelThreeSplits (nodeShapeAt node)).idxOf
    ((nodeShapeAt node).complement (splitShapeAt node slot))

def positiveNodeGlobalRow (node : ℕ) : ℕ :=
  shapeEightIndex (nodeShapeAt node) * 6 + node % 6

def edgeNode (edge : ℕ) : ℕ := edge / 60
def edgeRegion (edge : ℕ) : ℕ := edge / 10 % 6
def edgeSlot (edge : ℕ) : ℕ := edge % 10

/-- Exact 44-bit occurrence numerator of a level-two edge, using a precomputed level-three mass
table.  Generated checks seal that small table once and reuse it across all edge chunks. -/
def levelTwoMassNumeratorWithMass3
    (data : PrimaryTables) (mass3 : Array ℕ) (edge : ℕ) : ℕ :=
  let node := edgeNode edge
  let region := edgeRegion edge
  let slot := edgeSlot edge
  (mass3[positiveNodeGlobalRow node]?.getD 0) *
    dyadicNumeratorAt data.pos3A node region *
    (dyadicNumeratorAt data.pos3Alpha (node * 6 + region) slot +
      dyadicNumeratorAt data.pos3Alpha (node * 6 + region) (complementSlotAt node slot))

def levelTwoMassNumerator (data : PrimaryTables) (edge : ℕ) : ℕ :=
  levelTwoMassNumeratorWithMass3 data (levelThreeMassNumerators data) edge

def topZeroNumerator (data : PrimaryTables) (root shape : ℕ) : ℕ :=
  massNumeratorAt data.top (root * 48 + shape)

def zeroThreeShapeAt (row : ℕ) : Shape :=
  (shapes 8)[row / 6]?.getD default

def zeroFourShapeAt (shape : ℕ) : Shape :=
  MatrixMultiplication.LevelFourRemainingReconstruction.zeroFourShapes[shape]?.getD default

/-- Big-endian base-three digit order used by the Python `itertools.product` support tables. -/
def ternaryDigit (length code position : ℕ) : ℕ :=
  code / 3 ^ (length - 1 - position) % 3

def ternaryCodeWeight (length code : ℕ) : ℕ :=
  ((List.range length).map fun position => ternaryDigit length code position).sum

def ternaryCodeOnes (length code : ℕ) : ℕ :=
  ((List.range length).map fun position =>
    if ternaryDigit length code position = 1 then 1 else 0).sum

def ternarySupportCodes (length total : ℕ) : List ℕ :=
  (List.range (3 ^ length)).filter fun code => ternaryCodeWeight length code = total

def ternarySupportOnes (length total symbol : ℕ) : ℕ :=
  ternaryCodeOnes length ((ternarySupportCodes length total)[symbol]?.getD 0)

def ternarySupportOnesRows (length : ℕ) : Array (Array ℕ) :=
  ((List.range (2 * length + 1)).map fun total =>
    ((ternarySupportCodes length total).map (ternaryCodeOnes length)).toArray).toArray

def ternarySupportOnesFrom (rows : Array (Array ℕ)) (total symbol : ℕ) : ℕ :=
  (rows[total]?.getD #[])[symbol]?.getD 0

def ternarySupportOnesTwo : ℕ → ℕ → ℕ :=
  ternarySupportOnesFrom (ternarySupportOnesRows 2)

def ternarySupportOnesFour : ℕ → ℕ → ℕ :=
  ternarySupportOnesFrom (ternarySupportOnesRows 4)

def ternarySupportOnesEight : ℕ → ℕ → ℕ :=
  ternarySupportOnesFrom (ternarySupportOnesRows 8)

/-! ## The exact recurrence as a formal integer-log expression -/

def positiveEdgeForm (outer mu : ℕ) : LogLinearForm :=
  if outer = 0 then .zero
  else ⟨0, [⟨5, (outer * (2 * localDenominator - 2 * mu) : ℕ)⟩]⟩

def zeroRowForm (outerBits outer : ℕ) (entries : List (ℕ × ℕ))
    (ones : ℕ → ℕ) : LogLinearForm :=
  if outer = 0 then .zero
  else
    let lift := 2 ^ (commonBits - outerBits - localBits)
    let expectedOnes := (entries.map fun entry => entry.2 * ones entry.1).sum
    ⟨outer * localBits * localDenominator * lift,
      ⟨5, (outer * expectedOnes * lift : ℕ)⟩ ::
        entries.map fun entry => ⟨entry.2, -((outer * entry.2 * lift : ℕ) : ℤ)⟩⟩

def edgeFormWithMass3 (data : PrimaryTables) (mass3 : Array ℕ) (edge : ℕ) : LogLinearForm :=
  let node := edgeNode edge
  let slot := edgeSlot edge
  if splitSlotIsValid node slot then
    let outer := levelTwoMassNumeratorWithMass3 data mass3 edge
    let child := splitShapeAt node slot
    if child.IsPositive then
      positiveEdgeForm outer (scalarNumeratorAt data.mu edge)
    else
      zeroRowForm 44 outer (dyadicRowEntries data.edgeZero2 edge)
        (ternarySupportOnesTwo
          (MatrixMultiplication.LevelFourRemainingReconstruction.zeroLawTotal child))
  else .zero

def edgeForm (data : PrimaryTables) (edge : ℕ) : LogLinearForm :=
  edgeFormWithMass3 data (levelThreeMassNumerators data) edge

def zeroThreeFormWithMass3
    (data : PrimaryTables) (mass3 : Array ℕ) (row : ℕ) : LogLinearForm :=
  let shape := zeroThreeShapeAt row
  if shape.IsPositive then .zero
  else
    zeroRowForm topBits (mass3[row]?.getD 0) (dyadicRowEntries data.zero3 row)
      (ternarySupportOnesFour
        (MatrixMultiplication.LevelFourRemainingReconstruction.zeroLawTotal shape))

def zeroThreeForm (data : PrimaryTables) (row : ℕ) : LogLinearForm :=
  zeroThreeFormWithMass3 data (levelThreeMassNumerators data) row

def zeroFourForm (data : PrimaryTables) (flat : ℕ) : LogLinearForm :=
  let root := flat / 48
  let shapeIndex := flat % 48
  let shape := zeroFourShapeAt shapeIndex
  zeroRowForm topBits (topZeroNumerator data root shapeIndex) (dyadicRowEntries data.zero4 flat)
    (ternarySupportOnesEight
      (MatrixMultiplication.LevelFourRemainingReconstruction.zeroLawTotal shape))

def edgeRangeForm (data : PrimaryTables) (start count : ℕ) : LogLinearForm :=
  LogLinearForm.sum ((natInterval start count).map (edgeForm data))

def edgeRangeFormWithMass3 (data : PrimaryTables) (mass3 : Array ℕ)
    (start count : ℕ) : LogLinearForm :=
  LogLinearForm.sum ((natInterval start count).map (edgeFormWithMass3 data mass3))

theorem edgeRangeForm_eq_withMass3 (data : PrimaryTables) (start count : ℕ) :
    edgeRangeForm data start count =
      edgeRangeFormWithMass3 data (levelThreeMassNumerators data) start count := by
  rfl

def zeroThreeRangeForm (data : PrimaryTables) (start count : ℕ) : LogLinearForm :=
  LogLinearForm.sum ((natInterval start count).map (zeroThreeForm data))

def zeroThreeRangeFormWithMass3 (data : PrimaryTables) (mass3 : Array ℕ)
    (start count : ℕ) : LogLinearForm :=
  LogLinearForm.sum ((natInterval start count).map (zeroThreeFormWithMass3 data mass3))

theorem zeroThreeRangeForm_eq_withMass3 (data : PrimaryTables) (start count : ℕ) :
    zeroThreeRangeForm data start count =
      zeroThreeRangeFormWithMass3 data (levelThreeMassNumerators data) start count := by
  rfl

def zeroFourRangeForm (data : PrimaryTables) (start count : ℕ) : LogLinearForm :=
  LogLinearForm.sum ((natInterval start count).map (zeroFourForm data))

def edgeChunkCount : ℕ := 14
def edgeChunkSize : ℕ := 540
def zeroThreeChunkCount : ℕ := 3
def zeroThreeChunkSize : ℕ := 90
def zeroFourChunkCount : ℕ := 6
def zeroFourChunkSize : ℕ := 48

/-- Fixed moderate-size chunks keep the exact kernel checks below the project's memory budget. -/
def scalarRecurrenceChunks (data : PrimaryTables) : List LogLinearForm :=
  [edgeRangeForm data 0 540,
    edgeRangeForm data 540 540,
    edgeRangeForm data 1080 540,
    edgeRangeForm data 1620 540,
    edgeRangeForm data 2160 540,
    edgeRangeForm data 2700 540,
    edgeRangeForm data 3240 540,
    edgeRangeForm data 3780 540,
    edgeRangeForm data 4320 540,
    edgeRangeForm data 4860 540,
    edgeRangeForm data 5400 540,
    edgeRangeForm data 5940 540,
    edgeRangeForm data 6480 540,
    edgeRangeForm data 7020 540,
    zeroThreeRangeForm data 0 90,
    zeroThreeRangeForm data 90 90,
    zeroThreeRangeForm data 180 90,
    zeroFourRangeForm data 0 48,
    zeroFourRangeForm data 48 48,
    zeroFourRangeForm data 96 48,
    zeroFourRangeForm data 144 48,
    zeroFourRangeForm data 192 48,
    zeroFourRangeForm data 240 48]

/-- The full scalar sum `M_X + M_Y + M_Z`, before evaluating logarithms. -/
def scalarRecurrenceFormFrom (data : PrimaryTables) : LogLinearForm :=
  LogLinearForm.sum (scalarRecurrenceChunks data)

def scalarRecurrenceForm : LogLinearForm :=
  scalarRecurrenceFormFrom generatedPrimaryTables

/-- Real value of the exact scalar recurrence reconstructed from generated primary data. -/
def reconstructedScalarCoordinateSum : ℝ :=
  scalarRecurrenceForm.eval commonBits

/-! ## The compact generated target form -/

def positiveFamilyTerms {n : ℕ} (argument coefficient : Fin n → ℕ) : List LogTerm :=
  List.ofFn fun term => ⟨argument term, (coefficient term : ℕ)⟩

def negativeFamilyTerms {n : ℕ} (argument coefficient : Fin n → ℕ) : List LogTerm :=
  List.ofFn fun term => ⟨argument term, -((coefficient term : ℕ) : ℤ)⟩

open MatrixMultiplication.Generated.SimplifiedVolumeScalar

def scalarExpectedTerms : List LogTerm :=
  positiveFamilyTerms Positive.argument Positive.coefficient ++
    negativeFamilyTerms Negative0.argument Negative0.coefficient ++
    negativeFamilyTerms Negative1.argument Negative1.coefficient ++
    negativeFamilyTerms Negative2.argument Negative2.coefficient ++
    negativeFamilyTerms Negative3.argument Negative3.coefficient ++
    negativeFamilyTerms Negative4.argument Negative4.coefficient ++
    negativeFamilyTerms Negative5.argument Negative5.coefficient ++
    negativeFamilyTerms Negative6.argument Negative6.coefficient ++
    negativeFamilyTerms Negative7.argument Negative7.coefficient ++
    negativeFamilyTerms Negative8.argument Negative8.coefficient ++
    negativeFamilyTerms Negative9.argument Negative9.coefficient ++
    negativeFamilyTerms Negative10.argument Negative10.coefficient ++
    negativeFamilyTerms Negative11.argument Negative11.coefficient

def scalarExpectedForm : LogLinearForm :=
  ⟨MatrixMultiplication.Generated.SimplifiedVolumeScalar.constantNumerator,
    scalarExpectedTerms⟩

theorem termsValue_positiveFamilyTerms {n : ℕ} (argument coefficient : Fin n → ℕ) :
    LogLinearForm.termsValue commonBits (positiveFamilyTerms argument coefficient) =
      MatrixMultiplication.DyadicLogLinear.logSum commonBits argument coefficient := by
  unfold LogLinearForm.termsValue positiveFamilyTerms
  rw [List.map_ofFn, List.sum_ofFn]
  simp [LogLinearForm.termValue, MatrixMultiplication.DyadicLogLinear.logSum,
    mass, log2Nat]

theorem termsValue_negativeFamilyTerms {n : ℕ} (argument coefficient : Fin n → ℕ) :
    LogLinearForm.termsValue commonBits (negativeFamilyTerms argument coefficient) =
      -MatrixMultiplication.DyadicLogLinear.logSum commonBits argument coefficient := by
  unfold LogLinearForm.termsValue negativeFamilyTerms
  rw [List.map_ofFn, List.sum_ofFn]
  unfold MatrixMultiplication.DyadicLogLinear.logSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro term _
  simp [LogLinearForm.termValue, mass, log2Nat]
  ring

/-- Evaluation of the compact target form is definitionally the independently bounded generated
scalar certificate. -/
theorem scalarExpectedForm_eval :
    scalarExpectedForm.eval commonBits =
      MatrixMultiplication.Generated.SimplifiedVolumeScalar.scalarCoordinateSum := by
  simp only [LogLinearForm.eval, scalarExpectedForm, scalarExpectedTerms,
    LogLinearForm.termsValue_append]
  rw [termsValue_positiveFamilyTerms]
  rw [termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms,
    termsValue_negativeFamilyTerms, termsValue_negativeFamilyTerms]
  unfold MatrixMultiplication.Generated.SimplifiedVolumeScalar.scalarCoordinateSum
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.negativeExactSum
    Positive.exact Negative0.exact Negative1.exact Negative2.exact Negative3.exact
    Negative4.exact Negative5.exact Negative6.exact Negative7.exact Negative8.exact
    Negative9.exact Negative10.exact Negative11.exact
  simp only [commonBits,
    MatrixMultiplication.Generated.SimplifiedVolumeScalar.bits]
  ring

end

end MatrixMultiplication.SimplifiedVolumeReconstruction
