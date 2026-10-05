/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelTwoOrientedTypedLeaf
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetry
import AlgebraicComplexity.Probability.BinaryEntropy

set_option autoImplicit false

/-!
# The raw-square CW `(2,1,1)` rational typed leaf

This module exposes the `heavy = 0` specialization of the common oriented level-two typed-leaf
API under the literal raw-square `(2,1,1)` notation used by [CW90].  It checks that the existing
four-letter embedding has image exactly

`{200 ⊗ 011, 011 ⊗ 200, 101 ⊗ 110, 110 ⊗ 101}`,

records its normalized masses, rotates the canonical `(1,1,2)` entropy and dimension formulas,
and re-exports the existing genuine segmented degeneration certificate.  No restriction,
counting, or value argument is repeated here.

The canonical four-branch law and its shared-block geometry transcribe
`papers/notes/MMult1987.tex`, lines 174--218, while the entropy and exact-dimension interpretation
follows lines 261--285.  The literal raw `(2,1,1)` dictionary is the proved cyclic corollary of
that canonical `(1,1,2)` presentation, and the binary-entropy identity below is its elementary
algebraic rewrite.  The underlying source is D. Coppersmith and S. Winograd, *Matrix
Multiplication via Arithmetic Progressions* [CW90], Section 8 (journal pp. 270--272).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The literal raw `(2,1,1)` alphabet -/

/-- The rational typed leaf whose ternary interface has been rotated from `Z` to `X`.

This is definitionally the common oriented level-two leaf with heavy coordinate zero, the
orientation that the committed adapter identifies with the coarse square address `(2,1,1)`. -/
def cwSquare211RationalTypedLeaf
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :=
  cwLevelTwoRationalTypedLeaf q L G hq hL hG 0

/-- Embed the abstract four-letter profile into the honest uncoarsened tensor-square support. -/
noncomputable def cwSquare211FineLetter
    (K : Type u) [CommRing K] (q : ℕ) :
    cw112BlockSupport ↪ (cwChunkPartitionedTensor K q 1).support :=
  cwLevelTwoFineLetter K q 0

/-- The readable raw square address represented by each abstract four-letter source symbol.

The diagonal symbols become `011 ⊗ 200` and `200 ⊗ 011`; the cross symbols become
`110 ⊗ 101` and `101 ⊗ 110`, in that order. -/
def cwSquare211RawDictionary (source : cw112BlockSupport) :
    BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1) :=
  match source.1 .Z with
  | .firstCorner => cwSquareRawAddress cw011 cw200
  | .secondCorner => cwSquareRawAddress cw200 cw011
  | .grid =>
      match source.1 .X with
      | .first => cwSquareRawAddress cw110 cw101
      | .second => cwSquareRawAddress cw101 cw110

/-- The oriented fine-letter embedding is exactly the displayed raw dictionary, and its image is
the complete source fiber of the coarse square constituent `(2,1,1)`.

Proof sketch: inspect the four supported canonical `112` letters.  The committed heavy-zero
orientation cycles their block labels, producing the four raw words displayed above.  The second
claim then follows from the already proved exact description `cwSquareSourceFiber_211`. -/
theorem cwSquare211FineLetter_dictionary_image
    (K : Type u) [CommRing K] (q : ℕ) :
    (fun source : cw112BlockSupport ↦ (cwSquare211FineLetter K q source).1) =
        cwSquare211RawDictionary ∧
      Finset.univ.image cwSquare211RawDictionary =
        cwSquareSourceFiber cwSquare211 := by
  constructor
  · funext source
    rcases source with ⟨source, hsource⟩
    simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hsource
    rcases hsource with rfl | rfl | rfl | rfl
    all_goals
      funext c
      cases c <;> rfl
  · rw [cwSquareSourceFiber_211]
    decide

/-! ## Exact masses and entropy -/

/-- The derived binary-splitting parameter `β = 2μ = L / (L + G)`, represented exactly. -/
noncomputable def cwSquare211Beta (L G : ℕ) : ℝ :=
  (L : ℝ) / (L + G : ℕ)

/-- The normalized masses of the four dictionary entries are
`(β/2, β/2, (1-β)/2, (1-β)/2)`.

Through `cwSquare211RawDictionary`, the first pair is `011 ⊗ 200, 200 ⊗ 011` and the second pair
is `110 ⊗ 101, 101 ⊗ 110`.

Proof sketch: orientation does not alter the integral source profile `(L,L,G,G)`.  Divide those
four counts by its proved mass `2(L+G)` and rewrite using `β = L/(L+G)`. -/
theorem cwSquare211RationalTypedLeaf_normalized_masses
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cwSquare211RationalTypedLeaf q L G hq hL hG).distribution.weight
          cw112DiagonalFirstS = cwSquare211Beta L G / 2 ∧
      (cwSquare211RationalTypedLeaf q L G hq hL hG).distribution.weight
          cw112DiagonalSecondS = cwSquare211Beta L G / 2 ∧
      (cwSquare211RationalTypedLeaf q L G hq hL hG).distribution.weight
          cw112CrossFirstS = (1 - cwSquare211Beta L G) / 2 ∧
      (cwSquare211RationalTypedLeaf q L G hq hL hG).distribution.weight
          cw112CrossSecondS = (1 - cwSquare211Beta L G) / 2 := by
  have hweight (source : cw112BlockSupport) :
      (cwSquare211RationalTypedLeaf q L G hq hL hG).distribution.weight source =
        (cw112NaturalType L G source : ℝ) / (2 * (L + G) : ℕ) := by
    change (cw112IntegralProfile L G hL hG).probability.weight source = _
    rw [PositiveIntegralProfile.probability_weight, cw112IntegralProfile_mass]
    rfl
  have hsum : (0 : ℝ) < L + G := by
    exact_mod_cast Nat.add_pos_left hL G
  have hdiagonal :
      (L : ℝ) / (2 * (L + G) : ℕ) = cwSquare211Beta L G / 2 := by
    unfold cwSquare211Beta
    push_cast
    field_simp [hsum.ne']
  have hcross :
      (G : ℝ) / (2 * (L + G) : ℕ) = (1 - cwSquare211Beta L G) / 2 := by
    unfold cwSquare211Beta
    push_cast
    field_simp [hsum.ne']
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hweight]
    exact hdiagonal
  · rw [hweight]
    exact hdiagonal
  · rw [hweight]
    exact hcross
  · rw [hweight]
    exact hcross

/-- The ternary entropy in the canonical `112` formula is
`H₂(β) + β` in the literal raw-square parameterization.

Here `H₂(β)` is Mathlib's natural-log `Real.binEntropy β` divided by `log 2`.  This is the named
scalar identity behind the raw `(2,1,1)` entropy coordinate.

Proof sketch: write `μ = β/2`.  The two equal `μ` atoms arise by splitting the `β` event into two
equiprobable labels.  Algebraically, `negMulLog (β/2)` is expanded with
`Real.negMulLog_mul`, and each such split contributes half of `β log 2`. -/
theorem cwSquare211_muEntropyBits_eq_binaryEntropyBits_add_beta
    (L G : ℕ) (hLG : 0 < L + G) :
    cw112MuEntropyBits L G =
      Real.binEntropy (cwSquare211Beta L G) / Real.log 2 + cwSquare211Beta L G := by
  have hsum : (0 : ℝ) < L + G := by
    exact_mod_cast hLG
  have hmu : cw112Mu L G = cwSquare211Beta L G / 2 := by
    unfold cw112Mu cwSquare211Beta
    push_cast
    field_simp [hsum.ne']
  have hrest :
      1 - 2 * (cwSquare211Beta L G / 2) = 1 - cwSquare211Beta L G := by
    ring
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hhalfEntropy :
      Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
    rw [Real.negMulLog_eq_neg]
    change -((1 / 2 : ℝ) * Real.log (1 / 2)) = Real.log 2 / 2
    rw [hlogHalf]
    ring
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold cw112MuEntropyBits
  rw [hmu, hrest]
  rw [show cwSquare211Beta L G / 2 =
      cwSquare211Beta L G * (1 / 2 : ℝ) by ring]
  rw [Real.negMulLog_mul, hhalfEntropy,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  field_simp [hlogTwo]
  ring

/-- The literal `(2,1,1)` orientation has entropy tuple `(H₂(β)+β, 1, 1)`.

Proof sketch: the heavy-zero leaf is the forward cyclic permutation of the canonical `112` leaf.
Thus its `X` marginal is the canonical ternary `Z` marginal, while its `Y` and `Z` marginals are
the two balanced binary side marginals.  Apply the preceding scalar identity to the first. -/
theorem cwSquare211RationalTypedLeaf_marginalEntropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cwSquare211RationalTypedLeaf q L G hq hL hG).marginalEntropyBits c =
      match c with
      | .X => Real.binEntropy (cwSquare211Beta L G) / Real.log 2 + cwSquare211Beta L G
      | .Y => 1
      | .Z => 1 := by
  change (cw112RationalTypedLeaf q L G hq hL hG).marginalEntropyBits
    (cycle.symm c) = _
  cases c with
  | X =>
      rw [cycle_symm_X, cw112RationalTypedLeaf_z_entropyBits,
        cwSquare211_muEntropyBits_eq_binaryEntropyBits_add_beta L G
          (Nat.add_pos_left hL G)]
  | Y =>
      rw [cycle_symm_Y]
      exact cw112RationalTypedLeaf_side_entropyBits q L G hq hL hG .X (Or.inl rfl)
  | Z =>
      rw [cycle_symm_Z]
      exact cw112RationalTypedLeaf_side_entropyBits q L G hq hL hG .Y (Or.inr rfl)

/-! ## Exact dimensions and semantic certificate -/

/-- The exact dimension-product triple of the raw `(2,1,1)` leaf is
`(q^(2G), q^(2G), q^(2L))`.

Proof sketch: a forward cyclic orientation makes the new coordinates read canonical coordinates
`Z`, `X`, and `Y`, respectively.  The result is therefore just the three already proved canonical
dimension-product formulas in their rotated order. -/
theorem cwSquare211RationalTypedLeaf_dimensionProducts
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cwSquare211RationalTypedLeaf q L G hq hL hG).dimensionProduct c =
      match c with
      | .X => q ^ (2 * G)
      | .Y => q ^ (2 * G)
      | .Z => q ^ (2 * L) := by
  change (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct
    (cycle.symm c) = _
  cases c <;>
    simp only [cycle_symm_X, cycle_symm_Y, cycle_symm_Z,
      cw112RationalTypedLeaf_dimensionProduct_X,
      cw112RationalTypedLeaf_dimensionProduct_Y,
      cw112RationalTypedLeaf_dimensionProduct_Z]

/-- A proportional raw `(2,1,1)` word carries the existing genuine local polynomial-degeneration
certificate inside the uncoarsened CW square.

Proof sketch: specialize `cwLevelTwoSegmentedCertificate` to heavy coordinate zero.  Its embedded
word is exactly `cwSquare211FineLetter`, and the preceding module has already checked every
constituent restriction and exact dimension; this wrapper adds no semantic premise. -/
noncomputable def cwSquare211SegmentedCertificate
    (K : Type u) [CommRing K]
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {r k : ℕ}
    (word : PositiveWord cw112BlockSupport r)
    (hword : word ∈ positiveTypeClass cw112BlockSupport r
      (WordType.proportionalCounts
        (cwSquare211RationalTypedLeaf q L G hq hL hG).profile.count k)) :
    PolynomialDegenerates.SegmentedLeafCertificate
      (cwChunkPartitionedTensor K q 1) :=
  cwLevelTwoSegmentedCertificate K q L G hq hL hG 0 word hword

end AlgebraicComplexity.Examples
