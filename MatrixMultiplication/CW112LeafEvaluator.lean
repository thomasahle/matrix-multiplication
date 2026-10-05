import AlgebraicComplexity.Examples.CoppersmithWinograd112LeafInterface
import MatrixMultiplication.LevelFourRemainingReconstruction
import MatrixMultiplication.VolumeBounds
import Mathlib.Tactic.FinCases

/-!
# Level-two certificate entries as concrete CW `112` typed leaves

The recursive evaluator stores a positive level-two parameter as a 32-bit dyadic numerator `a`
with `0 < a < 2^31`.  This module translates that entry into the exact integral CW profile

`(L,L,G,G) = (a,a,2^31-a,2^31-a)`.

Consequently `mu = L / (2(L+G))` is exactly `a / 2^32`, rather than merely an approximation.
The main theorem also reconstructs the heavy coordinate of every positive total-four shape,
matches the evaluator's entropy branches with an oriented rational typed leaf, and identifies the
sum of the three dimension rates with `VolumeBounds.positiveEdgeValue`.

No generated numeral table is imported here.  A generated certificate only has to supply the
already executable `MuArrays.IsValid` theorem.
-/

open scoped BigOperators

namespace MatrixMultiplication.CW112LeafEvaluator

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData
open MatrixMultiplication.LevelFourRemainingReconstruction

noncomputable section

/-- Half of the certificate's 32-bit dyadic denominator. -/
def halfDenominator : ℕ := 2 ^ 31

/-- The checked half-denominator in `MuArrays.IsValid` is exactly `2^31`. -/
theorem certificate_halfDenominator_eq :
    AlgebraicComplexity.dyadicDenominator bits / 2 = halfDenominator := by
  norm_num [AlgebraicComplexity.dyadicDenominator, bits, halfDenominator]

/-- Integral `L` count represented by a certificate `mu` numerator. -/
def leafL (numerator : ℕ) : ℕ := numerator

/-- Integral `G` count completing a certificate numerator to half the dyadic denominator. -/
def leafG (numerator : ℕ) : ℕ := halfDenominator - numerator

/-- A numerator strictly below one half gives a positive `G` count. -/
theorem leafG_pos {numerator : ℕ} (hhalf : numerator < halfDenominator) :
    0 < leafG numerator := by
  exact Nat.sub_pos_of_lt hhalf

/-- The CW parameter reconstructed from the integral counts is exactly the evaluator's dyadic
mass `numerator / 2^32`.

Proof sketch: `numerator + (2^31 - numerator) = 2^31`, so the CW denominator
`2(L+G)` is `2^32`. -/
theorem cw112Mu_leafL_leafG_eq_mass
    {numerator : ℕ} (hhalf : numerator < halfDenominator) :
    cw112Mu (leafL numerator) (leafG numerator) =
      DyadicEntropy.mass bits numerator := by
  have hsum : numerator + (halfDenominator - numerator) = halfDenominator :=
    Nat.add_sub_of_le (Nat.le_of_lt hhalf)
  unfold cw112Mu leafL leafG DyadicEntropy.mass
  rw [hsum]
  norm_num [halfDenominator, bits]

/-- Evaluator entropy of a positive level-two branch with ternary law
`(mu,mu,1-2mu)`. -/
def positiveEdgeEntropyBits (mu : ℝ) : ℝ :=
  (2 * Real.negMulLog mu + Real.negMulLog (1 - 2 * mu)) / Real.log 2

/-- A retained-rate vector has entropy `H(mu,mu,1-2mu)` on its heavy coordinate and one bit on
the other two coordinates. -/
def positiveEdgeEntropyCoordinates
    (heavy : Fin 3) (entropy : ℝ) (coordinate : Fin 3) : ℝ :=
  if coordinate = heavy then entropy else 1

/-- Identify the evaluator's coordinates `0,1,2` with tensor legs `X,Y,Z`. -/
def finThreeLeg (coordinate : Fin 3) : Tensor.Leg :=
  if coordinate = 0 then Tensor.Leg.X
  else if coordinate = 1 then Tensor.Leg.Y
  else Tensor.Leg.Z

/-- Relabel the canonical CW entropy-special leg `Z` to an arbitrary evaluator heavy coordinate.
The other two coordinates both have entropy one, so their relative order is immaterial. -/
def entropyOrientation (heavy : Fin 3) : Equiv.Perm Tensor.Leg :=
  if heavy = 0 then Equiv.swap Tensor.Leg.Z Tensor.Leg.X
  else if heavy = 1 then Equiv.swap Tensor.Leg.Z Tensor.Leg.Y
  else Equiv.refl Tensor.Leg

/-- Oriented retained-rate vector supplied by one rational CW `112` typed leaf. -/
def orientedRetainedRateBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (heavy coordinate : Fin 3) : ℝ :=
  let leaf := cw112RationalTypedLeaf q L G hq hL hG
  permuteLegValues (entropyOrientation heavy)
    (fun c ↦ leaf.retainedRateBits leaf.distribution.entropyBits c)
    (finThreeLeg coordinate)

/-- The oriented typed-leaf retained rates are exactly the evaluator's positive-edge entropy
branches.

Proof sketch: in the canonical orientation the tuple is `(1,1,H(mu,mu,1-2mu))`; swapping the
canonical `Z` leg with `heavy` moves the sole nontrivial entry to the evaluator's chosen branch. -/
theorem orientedRetainedRateBits_eq
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (heavy coordinate : Fin 3) :
    orientedRetainedRateBits q L G hq hL hG heavy coordinate =
      positiveEdgeEntropyCoordinates heavy (cw112MuEntropyBits L G) coordinate := by
  fin_cases heavy <;> fin_cases coordinate <;>
    simp [orientedRetainedRateBits, entropyOrientation, finThreeLeg,
      positiveEdgeEntropyCoordinates, permuteLegValues,
      cw112RationalTypedLeaf_retainedRateBits, Equiv.swap_apply_of_ne_of_ne]

/-- Substituting the integral dyadic counts into the CW entropy gives the evaluator's exact
ternary entropy at the stored dyadic mass. -/
theorem cw112MuEntropyBits_leafL_leafG_eq
    {numerator : ℕ} (hhalf : numerator < halfDenominator) :
    cw112MuEntropyBits (leafL numerator) (leafG numerator) =
      positiveEdgeEntropyBits (DyadicEntropy.mass bits numerator) := by
  unfold cw112MuEntropyBits positiveEdgeEntropyBits
  rw [cw112Mu_leafL_leafG_eq_mass hhalf]

/-- The sum of the three primitive logarithmic dimension rates is the evaluator's
orientation-free positive-edge value `(2 - 2μ) log₂ q`.

Proof sketch: substitute the three checked coordinate rates
`((1-2μ), 2μ, (1-2μ)) log₂ q` and collect terms. -/
theorem cw112RationalTypedLeaf_sum_dimensionRateBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (∑ c, (cw112RationalTypedLeaf q L G hq hL hG).dimensionRateBits c) =
      (2 - 2 * cw112Mu L G) * cw112LogQBits q := by
  rw [Tensor.sum_leg, cw112RationalTypedLeaf_dimensionRateBits_X,
    cw112RationalTypedLeaf_dimensionRateBits_Y,
    cw112RationalTypedLeaf_dimensionRateBits_Z]
  ring

/-- The sum of the three matrix-dimension rates of the reconstructed typed leaf is precisely the
scalar positive-edge value consumed by the orientation-free volume recurrence. -/
theorem sum_dimensionRateBits_eq_positiveEdgeValue
    (q numerator : ℕ) (hq : 0 < q) (hL : 0 < leafL numerator)
    (hhalf : numerator < halfDenominator) :
    (∑ c, (cw112RationalTypedLeaf q (leafL numerator) (leafG numerator)
        hq hL (leafG_pos hhalf)).dimensionRateBits c) =
      VolumeBounds.positiveEdgeValue bits numerator q := by
  rw [cw112RationalTypedLeaf_sum_dimensionRateBits]
  rw [cw112Mu_leafL_leafG_eq_mass hhalf]
  rfl

/-- Read one of a shape's three coordinates using the evaluator's `Fin 3` convention. -/
def shapeCoordinate (shape : Shape) (c : Fin 3) : ℕ :=
  if c = 0 then shape.x else if c = 1 then shape.y else shape.z

/-- Reconstruct the evaluator's `heavy2 = shape.index(2)` convention for a positive level-two
shape.  The final branch is correct whenever the shape is positive of total four. -/
def shapeHeavyCoordinate (shape : Shape) : Fin 3 :=
  if shape.x = 2 then 0 else if shape.y = 2 then 1 else 2

/-- A positive total-four shape has value two at its reconstructed heavy coordinate. -/
theorem shapeCoordinate_heavyCoordinate_eq_two
    {shape : Shape} (hpositive : shape.IsPositive) (htotal : shape.total = 4) :
    shapeCoordinate shape (shapeHeavyCoordinate shape) = 2 := by
  rcases shape with ⟨x, y, z⟩
  simp only [Shape.IsPositive, Shape.total] at hpositive htotal
  simp only [shapeCoordinate, shapeHeavyCoordinate]
  split_ifs <;> omega

/-- Every non-heavy coordinate of a positive total-four shape has value one. -/
theorem shapeCoordinate_eq_one_of_ne_heavyCoordinate
    {shape : Shape} (hpositive : shape.IsPositive) (htotal : shape.total = 4)
    (c : Fin 3) (hc : c ≠ shapeHeavyCoordinate shape) :
    shapeCoordinate shape c = 1 := by
  rcases shape with ⟨x, y, z⟩
  simp only [Shape.IsPositive, Shape.total] at hpositive htotal
  fin_cases c <;> simp only [shapeCoordinate, shapeHeavyCoordinate] at hc ⊢ <;>
    split_ifs at hc ⊢ <;> omega

/-- A level-two slot selected by the level-four recursion whose child shape is one of the three
positive permutations of `(1,1,2)`. -/
def IsPositiveLevelTwoSlot (node : Fin nodeCount) (slot : Fin splitSlotCount) : Prop :=
  splitSlotValid node slot ∧ (splitShape node slot).IsPositive

/-- Semantic package expected of one positive level-two certificate entry: an exact rational CW
`112` typed leaf whose shape, entropy branches, and logarithmic matrix dimensions agree with the
recursive evaluator. -/
def InstantiatesCW112TypedLeaf
    (data : MuArrays) (q : ℕ) (hq : 0 < q)
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount) : Prop :=
  let numerator := data.muNumerator node region slot
  let L := leafL numerator
  let G := leafG numerator
  let heavy := shapeHeavyCoordinate (splitShape node slot)
  ∃ (hL : 0 < L) (hG : 0 < G),
    cw112Mu L G = DyadicEntropy.mass bits numerator ∧
    shapeCoordinate (splitShape node slot) heavy = 2 ∧
    (∀ c, c ≠ heavy → shapeCoordinate (splitShape node slot) c = 1) ∧
    (∀ c, orientedRetainedRateBits q L G hq hL hG heavy c =
      positiveEdgeEntropyCoordinates heavy
        (positiveEdgeEntropyBits (DyadicEntropy.mass bits numerator)) c) ∧
    (∑ c, (cw112RationalTypedLeaf q L G hq hL hG).dimensionRateBits c) =
      VolumeBounds.positiveEdgeValue bits numerator q

/-- **Certificate-facing CW `112` leaf theorem.**  Every selected positive level-two slot and
every valid stored `mu` entry instantiate a concrete rational CW typed leaf.  Its reconstructed
shape has the evaluator's advertised heavy-coordinate geometry, its oriented retained rates are
the exact `(1,1,H(mu,mu,1-2mu))` branches, and its total logarithmic matrix dimension is exactly
`VolumeBounds.positiveEdgeValue`.

Proof sketch: validity gives `0 < numerator < 2^31`; use it as `L` and complete it to
`G = 2^31-numerator`.  The preceding dyadic identities supply the rate formulas, while
`splitShape_geometry` shows that the selected positive child is a permutation of `(1,1,2)`. -/
theorem positiveLevelTwoSlot_instantiates_cw112
    (data : MuArrays) (hdata : data.IsValid)
    (q : ℕ) (hq : 0 < q)
    (node : Fin nodeCount) (region : Fin regionCount) (slot : Fin splitSlotCount)
    (hslot : IsPositiveLevelTwoSlot node slot) :
    InstantiatesCW112TypedLeaf data q hq node region slot := by
  unfold InstantiatesCW112TypedLeaf
  dsimp only
  have hL : 0 < leafL (data.muNumerator node region slot) := by
    simpa only [leafL] using MuArrays.muNumerator_pos hdata node region slot
  have hnHalfRaw := MuArrays.muNumerator_lt_half hdata node region slot
  have hhalf : data.muNumerator node region slot < halfDenominator := by
    rwa [certificate_halfDenominator_eq] at hnHalfRaw
  have hG : 0 < leafG (data.muNumerator node region slot) := leafG_pos hhalf
  refine ⟨hL, hG, cw112Mu_leafL_leafG_eq_mass hhalf, ?_, ?_, ?_, ?_⟩
  · exact shapeCoordinate_heavyCoordinate_eq_two hslot.2
      (splitShape_geometry node slot hslot.1).1
  · intro c hc
    exact shapeCoordinate_eq_one_of_ne_heavyCoordinate hslot.2
      (splitShape_geometry node slot hslot.1).1 c hc
  · intro c
    rw [orientedRetainedRateBits_eq]
    rw [cw112MuEntropyBits_leafL_leafG_eq hhalf]
  · exact sum_dimensionRateBits_eq_positiveEdgeValue q _ hq hL hhalf

end

end MatrixMultiplication.CW112LeafEvaluator
