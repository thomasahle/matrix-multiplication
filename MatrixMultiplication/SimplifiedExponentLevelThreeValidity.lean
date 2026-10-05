import MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
import MatrixMultiplication.SignedDyadicLogCanonical

/-!
# Executable validity checks for level-three constituent rows

The mathematical soundness theorem for an integer-product dual consumes
`LocalRows.IsValid`.  Generated certificate modules should not have to replay the projection from
a checked Boolean list by hand, so this module isolates that small trusted adapter.  The Boolean
checker is executable on a bounded explicit node chunk; `localRows_isValid_of_mem` turns one
kernel-checked chunk equality into the proposition required by the semantic recurrence.

Every quotient-dependent checker and semantic adapter has a `For` form taking the quotient slot
map explicitly.  The original declarations remain sorted-pair specializations for compatibility.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelThreeValidity

open MatrixMultiplication.SimplifiedExponentCompleteSplitRecurrence
open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
open MatrixMultiplication.SimplifiedExponentRecursiveConstituent
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.SignedDyadicLogForm

/-- Extensionality for serialized local rows, including their three finite weight functions. -/
theorem localRows_ext {left right : LocalRows coordinateCount}
    (hsupport : left.support = right.support)
    (hreference : left.referenceNumerators = right.referenceNumerators)
    (hmarginal : left.marginalXNumerators = right.marginalXNumerators)
    (hweightX : left.weightX = right.weightX)
    (hweightY : left.weightY = right.weightY)
    (hweightZ : left.weightZ = right.weightZ)
    (hlogicalY : left.logicalY = right.logicalY)
    (hlogicalZ : left.logicalZ = right.logicalZ) : left = right := by
  cases left
  cases right
  simp_all

/-- Extensionality for an outer-weighted serialized local row. -/
theorem weightedLocalRows_ext {left right : WeightedLocalRows coordinateCount}
    (houter : left.outerNumerator = right.outerNumerator)
    (hrows : left.rows = right.rows) : left = right := by
  cases left
  cases right
  simp_all

/-- Executable version of `LocalRows.IsValid`.  The three universal positivity fields are checked
on explicit `List.ofFn` enumerations, rather than asking typeclass search for a decision procedure
for a quantified proposition.  This keeps generated row checks fully reducible. -/
def localRowsValid (rows : LocalRows coordinateCount) : Bool :=
  decide (0 < rows.support.length) &&
    (decide (rows.referenceNumerators = List.ofFn rows.referenceNumerator) &&
      (decide (rows.marginalXNumerators =
        List.ofFn (marginalNumerator rows.coordinateX rows.referenceNumerator)) &&
        ((List.ofFn rows.weightX).all (fun value ↦ decide (0 < value)) &&
          ((List.ofFn rows.weightY).all (fun value ↦ decide (0 < value)) &&
            (List.ofFn rows.weightZ).all (fun value ↦ decide (0 < value))))))

/-- Soundness of the bounded Boolean row checker. -/
theorem localRows_isValid_of_valid
    (rows : LocalRows coordinateCount) (hvalid : localRowsValid rows = true) :
    rows.IsValid := by
  unfold localRowsValid at hvalid
  obtain ⟨hsupport, hrest⟩ := Bool.and_eq_true_iff.mp hvalid
  obtain ⟨hreference, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hmarginal, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hweightX, hrest⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hweightY, hweightZ⟩ := Bool.and_eq_true_iff.mp hrest
  refine ⟨of_decide_eq_true hsupport, of_decide_eq_true hreference,
    of_decide_eq_true hmarginal, ?_, ?_, ?_⟩
  · intro x
    exact of_decide_eq_true
      ((List.all_eq_true.mp hweightX) _ (List.mem_ofFn.mpr ⟨x, rfl⟩))
  · intro y
    exact of_decide_eq_true
      ((List.all_eq_true.mp hweightY) _ (List.mem_ofFn.mpr ⟨y, rfl⟩))
  · intro z
    exact of_decide_eq_true
      ((List.all_eq_true.mp hweightZ) _ (List.mem_ofFn.mpr ⟨z, rfl⟩))

/-- Check all row conditions on an explicit node list for a supplied quotient slot map. -/
def rowsValidOnNodesFor (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (weights : ℕ → DualWeights) (region : ℕ) (nodes : List ℕ) : Bool :=
  nodes.all fun node ↦
    localRowsValid (localRowsFor supportSlot data order (weights node) node region)

/-- Sorted-pair specialization of the bounded row checker. -/
def rowsValidOnNodes (data : PrimaryTables) (order : CoordinateOrder)
    (weights : ℕ → DualWeights) (region : ℕ) (nodes : List ℕ) : Bool :=
  rowsValidOnNodesFor sortedPairSupportSlot data order weights region nodes

/-- A successful quotient-parametric checker proves validity of every named local row. -/
theorem localRowsFor_isValid_of_mem (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (order : CoordinateOrder)
    (weights : ℕ → DualWeights) (region : ℕ) (nodes : List ℕ)
    (hvalid : rowsValidOnNodesFor supportSlot data order weights region nodes = true)
    {node : ℕ} (hnode : node ∈ nodes) :
    (localRowsFor supportSlot data order (weights node) node region).IsValid := by
  exact localRows_isValid_of_valid _ ((List.all_eq_true.mp hvalid) node hnode)

/-- A successful bounded checker supplies the semantic `LocalRows.IsValid` proposition for every
serialized node in the chunk. -/
theorem localRows_isValid_of_mem (data : PrimaryTables) (order : CoordinateOrder)
    (weights : ℕ → DualWeights) (region : ℕ) (nodes : List ℕ)
    (hvalid : rowsValidOnNodes data order weights region nodes = true)
    {node : ℕ} (hnode : node ∈ nodes) :
    (localRows data order (weights node) node region).IsValid := by
  exact localRowsFor_isValid_of_mem sortedPairSupportSlot
    data order weights region nodes hvalid hnode

/-- A quotient-parametric canonical form has exactly the semantic branch value reconstructed
from the corresponding primary rows. -/
theorem branchRateOnNodesFor_eq_eval_of_canonical
    (supportSlot : ℕ → ℕ → ℕ)
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ) (branch : Fin 3) (expected : Form)
    (hcanonical :
      Form.canonical (Form.normalizePowersOfTwo
        (branchFormOnNodesFor supportSlot data massThree orders weights region nodes branch)) =
          expected) :
    branchRateOnNodesFor supportSlot data massThree orders weights region nodes branch =
      Form.eval ((referenceBits + compatibilityExtraBits) + outerBits) expected := by
  have heval := congrArg
    (Form.eval ((referenceBits + compatibilityExtraBits) + outerBits)) hcanonical
  rw [Form.eval_canonical, Form.eval_normalizePowersOfTwo,
    branchFormOnNodesFor_eval] at heval
  exact heval

/-- A syntactically checked canonical form has exactly the semantic branch value reconstructed
from the primary rows.  This is the small reusable bridge used by generated row snapshots. -/
theorem branchRateOnNodes_eq_eval_of_canonical
    (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : ℕ) (nodes : List ℕ) (branch : Fin 3) (expected : Form)
    (hcanonical :
      Form.canonical (Form.normalizePowersOfTwo
        (branchFormOnNodes data massThree orders weights region nodes branch)) = expected) :
    branchRateOnNodes data massThree orders weights region nodes branch =
      Form.eval ((referenceBits + compatibilityExtraBits) + outerBits) expected := by
  exact branchRateOnNodesFor_eq_eval_of_canonical sortedPairSupportSlot
    data massThree orders weights region nodes branch expected hcanonical

end MatrixMultiplication.SimplifiedExponentLevelThreeValidity
