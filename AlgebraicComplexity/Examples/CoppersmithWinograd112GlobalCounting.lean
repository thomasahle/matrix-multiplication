/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112Global
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.MatrixMultiplication.CTensorCounting
import Mathlib.NumberTheory.Bertrand

/-!
# Aggregate counting for the global CW `112` extraction

This leaf module derives the finite square-count inequality from the semantic global extraction.
It also flattens the natural nested shared-Z/antidiagonal output into exactly `Fin count` copies
of one square matrix-multiplication tensor.  It is kept separate so downstream clients that need
only the finite `112` restriction, shared-Z grouping, and C-tensor degeneration do not pay to
elaborate the later quantitative argument.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

section TensorPower

universe u

variable (K : Type u) [CommRing K]
variable (q L G : ℕ)
variable {R : Type*} [Field R] [NeZero (2 : R)]

/-- Total number of square matrix-multiplication tensors in the nested extracted family. -/
noncomputable def cw112ExtractedSquareCount
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) : ℕ :=
  ∑ z : cw112OccupiedZWords L G B seed,
    (CTensor.antidiagonal
      (cw112ZFiberRetyping (K := K) q L G B hB seed z.1).targetConstituent).support.card

/-- The dependent pair indexing all extracted squares has cardinality
`cw112ExtractedSquareCount`.

Proof sketch: cardinality of a sigma type is the sum of the cardinalities of its fibers; each
inner index is the subtype of one C-tensor antidiagonal support. -/
theorem card_cw112ExtractedSquareIndex
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Fintype.card
        (Σ z : cw112OccupiedZWords L G B seed,
          (CTensor.antidiagonal
            (cw112ZFiberRetyping
              (K := K) q L G B hB seed z.1).targetConstituent).support) =
      cw112ExtractedSquareCount K q L G B hB seed := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe, cw112ExtractedSquareCount]

/-- Every occupied shared-Z word has the prescribed marginal multiplicities `(L,L,2G)`.

Proof sketch: choose a retained address in the nonempty fiber.  XY-isolated addresses remain in
the modeled legal-target family, hence come from a selected joint-type word.  Projecting that
word to Z gives the required marginal type, while fiber membership identifies the projection
with the original occupied Z word. -/
theorem cw112OccupiedZWords_subset_zTypeClass
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    cw112OccupiedZWords L G B seed ⊆
      positiveTypeClass CW112ZBlock (cw112TypeDepth L G)
        (cw112ZMarginalType L G) := by
  classical
  intro z hz
  have hzNonempty : (cw112XYIsolatedZFiber L G B seed z).Nonempty :=
    (mem_cw112OccupiedZWords L G B seed z).mp hz
  obtain ⟨address, haddress⟩ := hzNonempty
  have hfiber := Finset.mem_filter.mp haddress
  let H := cw112PartitionHashEncoding (R := R)
  have hmodeled : address ∈
      H.modeledAddresses (cw112TypeDepth L G)
        (H.legalTargets (cw112TypeDepth L G) (cw112TypeWords L G)) :=
    (H.xyIsolatedPowerAddresses_subset_filteredPowerAddresses
      (cw112TypeDepth L G) (cw112TypeWords L G) B seed).trans
        (H.filteredPowerAddresses_subset_modeledAddresses
          (cw112TypeDepth L G) (cw112TypeWords L G) B seed) hfiber.1
  obtain ⟨word, hword, hwordAddress⟩ :=
    H.exists_sourceWord_of_mem_modeledAddresses_legalTargets
      (cw112TypeDepth L G) (cw112TypeWords L G) hmodeled
  have hzAddress :
      PartitionHashEncoding.supportWordAddress
          (A := CW112Block) (support := cw112BlockSupport)
          (cw112TypeDepth L G) word .Z = z := by
    rw [hwordAddress]
    exact hfiber.2
  have hzmarginal := cw112LegWord_mem_marginalTypeClass L G word hword .Z
  rw [hzAddress] at hzmarginal
  exact mem_positiveTypeClass.mpr (WordType.mem_typeClass.mp hzmarginal)

/-- The number of occupied shared-Z fibers is at most the full Z marginal type-class size. -/
theorem card_cw112OccupiedZWords_le_zTypeClass
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    (cw112OccupiedZWords L G B seed).card ≤
      (WordType.typeClass (cw112TypeDepth L G + 1)
        (cw112ZMarginalType L G)).card := by
  calc
    (cw112OccupiedZWords L G B seed).card ≤
        (positiveTypeClass CW112ZBlock (cw112TypeDepth L G)
          (cw112ZMarginalType L G)).card :=
      Finset.card_le_card (cw112OccupiedZWords_subset_zTypeClass L G B seed)
    _ = (WordType.typeClass (cw112TypeDepth L G + 1)
          (cw112ZMarginalType L G)).card :=
      card_positiveTypeClass (cw112TypeDepth L G) (cw112ZMarginalType L G)

/-- The number of retained X/Y-isolated addresses is the sum of the occupied Z-fiber sizes.

Proof sketch: partition all retained addresses by their Z word.  Fibers outside
`cw112OccupiedZWords` are empty and therefore contribute zero; rewrite the remaining finite sum
as a sum over the occupied subtype. -/
theorem card_cw112XYIsolated_eq_sum_occupiedZFiber_card
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
      (cw112TypeDepth L G) (cw112TypeWords L G) B seed).card =
      ∑ z : cw112OccupiedZWords L G B seed,
        (cw112XYIsolatedZFiber L G B seed z.1).card := by
  classical
  let selected := (cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
    (cw112TypeDepth L G) (cw112TypeWords L G) B seed
  have hpartition : selected.card =
      ∑ z : PositiveWord CW112ZBlock (cw112TypeDepth L G),
        (selected.filter fun s ↦ s .Z = z).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := selected)
        (t := (Finset.univ : Finset
          (PositiveWord CW112ZBlock (cw112TypeDepth L G))))
        (f := fun s ↦ s .Z) (fun _s _hs ↦ Finset.mem_univ _))
  rw [show ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
      (cw112TypeDepth L G) (cw112TypeWords L G) B seed) = selected by rfl]
  rw [hpartition]
  change (∑ z : PositiveWord CW112ZBlock (cw112TypeDepth L G),
      (cw112XYIsolatedZFiber L G B seed z).card) = _
  calc
    (∑ z : PositiveWord CW112ZBlock (cw112TypeDepth L G),
        (cw112XYIsolatedZFiber L G B seed z).card) =
        ∑ z ∈ cw112OccupiedZWords L G B seed,
          (cw112XYIsolatedZFiber L G B seed z).card := by
      symm
      apply Finset.sum_subset (Finset.subset_univ (cw112OccupiedZWords L G B seed))
      intro z _hz hnot
      have hempty : cw112XYIsolatedZFiber L G B seed z = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        simpa using hnot
      simp [hempty]
    _ = ∑ z : cw112OccupiedZWords L G B seed,
          (cw112XYIsolatedZFiber L G B seed z.1).card :=
      Finset.sum_subtype (cw112OccupiedZWords L G B seed) (fun _ ↦ Iff.rfl)
        (fun z ↦ (cw112XYIsolatedZFiber L G B seed z).card)

/-- Global division-free lower bound for the number of squares extracted from the exceptional
`112` constituent:

`retainedAddresses² ≤ 2 * occupiedZFibers * extractedSquares`.

Proof sketch: rewrite the retained-address count as the sum of occupied fiber sizes, then apply
the reusable aggregate C-tensor antidiagonal inequality. -/
theorem sq_card_cw112XYIsolated_le_two_mul_occupied_mul_extracted
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
      (cw112TypeDepth L G) (cw112TypeWords L G) B seed).card ^ 2 ≤
      2 * (cw112OccupiedZWords L G B seed).card *
        cw112ExtractedSquareCount K q L G B hB seed := by
  rw [card_cw112XYIsolated_eq_sum_occupiedZFiber_card L G B seed]
  have haggregate :=
    CTensor.sq_sum_le_two_mul_card_mul_sum_card_antidiagonal
      (K := K)
      (h := fun z : cw112OccupiedZWords L G B seed ↦
        (cw112XYIsolatedZFiber L G B seed z.1).card)
      (T := fun z : cw112OccupiedZWords L G B seed ↦
        (cw112ZFiberRetyping
          (K := K) q L G B hB seed z.1).targetConstituent)
  rw [Fintype.card_coe] at haggregate
  simpa only [cw112ExtractedSquareCount] using haggregate

/-- The complete finite `112` extraction can be presented as exactly
`cw112ExtractedSquareCount` identical square matrix-multiplication tensors.

The semantic extraction in `CoppersmithWinograd112Global` deliberately retains its natural
nested indexing: first an occupied shared-Z word, then an antidiagonal address in that fiber.
This theorem flattens that dependent sum and reindexes it by `Fin` of its proved cardinality,
which is the form consumed by the uniform asymptotic laser interfaces.

Proof sketch: apply the proved degeneration to the nested square family, invert the canonical
sigma-currying tensor isomorphism, and finally reindex the resulting constant direct sum along
`Fintype.equivFinOfCardEq`. -/
theorem cw112PowerCyclicProduct_degenerates_flatSquareFamily
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    PolynomialDegenerates
      (cw112PowerCyclicProduct K q L G)
      (matrixMultiplicationDirectSum
        (ι := Fin (cw112ExtractedSquareCount K q L G B hB seed)) K
        (fun _ ↦ cw112FiniteLeafSquareSide q L G)
        (fun _ ↦ cw112FiniteLeafSquareSide q L G)
        (fun _ ↦ cw112FiniteLeafSquareSide q L G)) := by
  classical
  let I :=
    Σ z : cw112OccupiedZWords L G B seed,
      (CTensor.antidiagonal
        (cw112ZFiberRetyping
          (K := K) q L G B hB seed z.1).targetConstituent).support
  let Q := matrixMultiplication (K := K)
    (cw112FiniteLeafSquareSide q L G)
    (cw112FiniteLeafSquareSide q L G)
    (cw112FiniteLeafSquareSide q L G)
  let flatFamily := Tensor.indexedDirectSum (fun _ : I ↦ Q)
  have hnested :=
    cw112PowerCyclicProduct_degenerates_squareFamilies
      K q L G B hB seed
  have hflatten :
      Restricts (cw112FiniteLeafSquareFamilies K q L G B hB seed) flatFamily := by
    have hsigma := Tensor.Isomorphic.indexedDirectSum_sigma
      (K := K)
      (J := fun z : cw112OccupiedZWords L G B seed ↦
        (CTensor.antidiagonal
          (cw112ZFiberRetyping
            (K := K) q L G B hB seed z.1).targetConstituent).support)
      (S := fun _z _address ↦ MMSpace K
        (cw112FiniteLeafSquareSide q L G)
        (cw112FiniteLeafSquareSide q L G)
        (cw112FiniteLeafSquareSide q L G))
      (T := fun _ : I ↦ Q)
    exact hsigma.symm.restricts
  have hcard : Fintype.card I = cw112ExtractedSquareCount K q L G B hB seed := by
    simpa only [I] using card_cw112ExtractedSquareIndex K q L G B hB seed
  let e : I ≃ Fin (cw112ExtractedSquareCount K q L G B hB seed) :=
    Fintype.equivFinOfCardEq hcard
  have hreindex : Restricts flatFamily
      (matrixMultiplicationDirectSum
        (ι := Fin (cw112ExtractedSquareCount K q L G B hB seed)) K
        (fun _ ↦ cw112FiniteLeafSquareSide q L G)
        (fun _ ↦ cw112FiniteLeafSquareSide q L G)
        (fun _ ↦ cw112FiniteLeafSquareSide q L G)) := by
    simpa only [flatFamily, Q, matrixMultiplicationDirectSum] using
      (Tensor.Restricts.indexedDirectSum_const_equiv
        (K := K) e Q)
  exact hnested.trans
    (PolynomialDegenerates.of_restricts (hflatten.trans hreindex))

/-- Exact finite quantitative endpoint for the exceptional `112` constituent.

For every positive integral type and every sufficiently large finite hashing field, one seed
simultaneously provides

* a degeneration to `cw112ExtractedSquareCount` equal square matrix-multiplication tensors; and
* the division-free count bound

`9 * jointWords^2 * |B|^2 ≤
  32 * |R|^4 * occupiedZFibers * extractedSquares`.

No asymptotic notation is hidden in this theorem.  Subsequent clients may bound the joint word
count below, the occupied-Z count above, and the field/AP-set losses subexponentially.

Proof sketch: choose the two-leg hashing seed, square its retained-address inequality, and use
`retainedAddresses² ≤ 2 * occupiedZFibers * extractedSquares`.  The semantic conclusion is
the flattened global degeneration proved above for the same seed. -/
theorem exists_cw112_flatSquareFamily_with_count
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    {L G : ℕ} (hLG : 0 < L + G)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hfield : 8 * cw112XYFiberSize L G ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)),
      9 * (cw112TypeTargets (R := R) L G).card ^ 2 * B.card ^ 2 ≤
          32 * (Fintype.card R) ^ 4 *
            (cw112OccupiedZWords L G B seed).card *
              cw112ExtractedSquareCount K q L G B hB seed ∧
        PolynomialDegenerates
          (cw112PowerCyclicProduct K q L G)
          (matrixMultiplicationDirectSum
            (ι := Fin (cw112ExtractedSquareCount K q L G B hB seed)) K
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)) := by
  obtain ⟨seed, hhash, _hfiltered, _hx, _hy⟩ :=
    exists_cw112_many_xyIsolatedTargets (R := R) hLG B hB hfield
  refine ⟨seed, ?_,
    cw112PowerCyclicProduct_degenerates_flatSquareFamily
      K q L G B hB seed⟩
  have haggregate :=
    sq_card_cw112XYIsolated_le_two_mul_occupied_mul_extracted
      K q L G B hB seed
  rw [card_cw112XYIsolatedPowerAddresses L G B seed] at haggregate
  calc
    9 * (cw112TypeTargets (R := R) L G).card ^ 2 * B.card ^ 2 =
        (3 * (cw112TypeTargets (R := R) L G).card * B.card) ^ 2 := by ring
    _ ≤ (4 * (Fintype.card R * Fintype.card R) *
          (ProgressionHash.LegalTriple.xyIsolatedTargets
            (cw112TypeTargets (R := R) L G) B seed).card) ^ 2 :=
      Nat.pow_le_pow_left hhash 2
    _ = 16 * (Fintype.card R) ^ 4 *
          (ProgressionHash.LegalTriple.xyIsolatedTargets
            (cw112TypeTargets (R := R) L G) B seed).card ^ 2 := by ring
    _ ≤ 16 * (Fintype.card R) ^ 4 *
          (2 * (cw112OccupiedZWords L G B seed).card *
            cw112ExtractedSquareCount K q L G B hB seed) :=
      Nat.mul_le_mul_left _ haggregate
    _ = 32 * (Fintype.card R) ^ 4 *
          (cw112OccupiedZWords L G B seed).card *
            cw112ExtractedSquareCount K q L G B hB seed := by ring

/-- Finite `112` endpoint with the seed-dependent occupied-fiber count replaced by the full,
explicit Z marginal type-class count.

This is the preferred quantitative interface for asymptotics: every factor except the extracted
copy count is determined before choosing the hashing seed. -/
theorem exists_cw112_flatSquareFamily_with_marginal_count
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    {L G : ℕ} (hLG : 0 < L + G)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hfield : 8 * cw112XYFiberSize L G ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)),
      9 * (cw112TypeTargets (R := R) L G).card ^ 2 * B.card ^ 2 ≤
          32 * (Fintype.card R) ^ 4 *
            (WordType.typeClass (cw112TypeDepth L G + 1)
              (cw112ZMarginalType L G)).card *
                cw112ExtractedSquareCount K q L G B hB seed ∧
        PolynomialDegenerates
          (cw112PowerCyclicProduct K q L G)
          (matrixMultiplicationDirectSum
            (ι := Fin (cw112ExtractedSquareCount K q L G B hB seed)) K
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)) := by
  obtain ⟨seed, hcount, hdeg⟩ :=
    exists_cw112_flatSquareFamily_with_count K q hLG B hB hfield
  refine ⟨seed, hcount.trans ?_, hdeg⟩
  have hz := card_cw112OccupiedZWords_le_zTypeClass L G B seed
  calc
    32 * (Fintype.card R) ^ 4 *
          (cw112OccupiedZWords L G B seed).card *
            cw112ExtractedSquareCount K q L G B hB seed ≤
        32 * (Fintype.card R) ^ 4 *
          (WordType.typeClass (cw112TypeDepth L G + 1)
            (cw112ZMarginalType L G)).card *
              cw112ExtractedSquareCount K q L G B hB seed := by
      gcongr

/-- Prime-cyclic-field realization of the finite `112` endpoint.

The progression-free set has the canonical cardinality `rothNumberNat (M/2)`.  All hashing,
shared-Z grouping, C-tensor degeneration, and the replacement of occupied fibers by the full Z
type class are discharged. -/
theorem exists_cw112_flatSquareFamily_with_marginal_count_zmod
    (M : ℕ) [Fact M.Prime]
    {L G : ℕ} (hLG : 0 < L + G)
    (hfield : 8 * cw112XYFiberSize L G ≤ M) :
    ∃ B : Finset (ZMod M),
      B.card = rothNumberNat (M / 2) ∧ ThreeAPFree (B : Set (ZMod M)) ∧
        ∃ copies : ℕ,
          9 * (cw112TypeWords L G).card ^ 2 * B.card ^ 2 ≤
              32 * M ^ 4 *
                (WordType.typeClass (cw112TypeDepth L G + 1)
                  (cw112ZMarginalType L G)).card * copies ∧
            PolynomialDegenerates
              (cw112PowerCyclicProduct K q L G)
              (matrixMultiplicationDirectSum
                (ι := Fin copies) K
                (fun _ ↦ cw112FiniteLeafSquareSide q L G)
                (fun _ ↦ cw112FiniteLeafSquareSide q L G)
                (fun _ ↦ cw112FiniteLeafSquareSide q L G)) := by
  have hd : 0 < cw112XYFiberSize L G := by
    rw [cw112XYFiberSize_eq_choose_sq hLG]
    have hchoose : 0 < Nat.choose (L + G) L :=
      Nat.choose_pos (Nat.le_add_right L G)
    positivity
  have hM : 3 ≤ M := by omega
  letI : NeZero (2 : ZMod M) := neZero_two_zmod_of_three_le hM
  obtain ⟨B, hBcard, hB⟩ := exists_threeAPFree_zmod_half M
  obtain ⟨seed, hcount, hdeg⟩ :=
    exists_cw112_flatSquareFamily_with_marginal_count
      K q hLG B hB (by simpa [ZMod.card] using hfield)
  let copies := cw112ExtractedSquareCount K q L G B hB seed
  refine ⟨B, hBcard, hB, copies, ?_, ?_⟩
  · simpa only [ZMod.card, card_cw112TypeTargets, copies] using hcount
  · simpa only [copies] using hdeg

/-- Purely numerical finite `112` extraction after choosing the hashing modulus by Bertrand's
postulate.

The prime lies between `8d` and `16d`, where `d` is the exact X/Y typed-fiber size.  The theorem
exposes only the copy count and deterministic type-class factors; the field, seed, and
progression-free set have been eliminated from the downstream interface. -/
theorem exists_prime_cw112_flatSquareFamily_with_marginal_count
    {L G : ℕ} (hLG : 0 < L + G) :
    ∃ M copies : ℕ,
      M.Prime ∧
        8 * cw112XYFiberSize L G < M ∧
        M ≤ 16 * cw112XYFiberSize L G ∧
        9 * (cw112TypeWords L G).card ^ 2 * rothNumberNat (M / 2) ^ 2 ≤
          32 * M ^ 4 *
            (WordType.typeClass (cw112TypeDepth L G + 1)
              (cw112ZMarginalType L G)).card * copies ∧
        PolynomialDegenerates
          (cw112PowerCyclicProduct K q L G)
          (matrixMultiplicationDirectSum (ι := Fin copies) K
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)
            (fun _ ↦ cw112FiniteLeafSquareSide q L G)) := by
  have hd : 0 < cw112XYFiberSize L G := by
    rw [cw112XYFiberSize_eq_choose_sq hLG]
    have hchoose : 0 < Nat.choose (L + G) L :=
      Nat.choose_pos (Nat.le_add_right L G)
    positivity
  have hbase : 8 * cw112XYFiberSize L G ≠ 0 := by positivity
  obtain ⟨M, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (8 * cw112XYFiberSize L G) hbase
  letI : Fact M.Prime := ⟨hprime⟩
  obtain ⟨B, hBcard, _hB, copies, hcount, hdeg⟩ :=
    exists_cw112_flatSquareFamily_with_marginal_count_zmod
      K q M hLG hlower.le
  refine ⟨M, copies, hprime, hlower, ?_, ?_, ?_⟩
  · calc
      M ≤ 2 * (8 * cw112XYFiberSize L G) := hupper
      _ = 16 * cw112XYFiberSize L G := by ring
  · simpa only [hBcard, card_cw112TypeTargets] using hcount
  · exact hdeg

end TensorPower

end AlgebraicComplexity.Examples
