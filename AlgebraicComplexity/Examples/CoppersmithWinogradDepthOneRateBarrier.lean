/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquare
import AlgebraicComplexity.Probability.EntropyCardinality
import AlgebraicComplexity.Probability.EntropyMixture

/-!
# The depth-one total-weight rate barrier for Coppersmith--Winograd chunks

A depth-one native CW chunk is an ordered pair of the six base support addresses, hence has a
36-letter fine alphabet.  Coarsening records the three coordinatewise degree sums.  This file
separates a chunk according to whether either base address is one of the three corner
constituents and proves the structural entropy bound

`min_c (H₂(C,L_c) - 2 H₂(C)) ≤ H₂(B) + P(B=true)`.

Here `C` is the total-weight coarse shape, `L_c` is the ordered fine block word on leg `c`, and
`B` is the corner-containing event.  The left side is exactly
`min_c (H₂(L_c | C) - H₂(C))`, the exponent occurring in the old global-competitor inner hashing
bound.  The proof has two finite inputs:

* every fixed coarse fiber contains at most two letters of either event class; and
* on the no-corner class, every modal coarse shape has a leg whose fine word is constant.

Both inputs are closed computations over the 36 letters.  The information-theoretic assembly is
generic and uses `Conditioning`, `EntropyMixture`, and the two-point support bound.  The later
numeric step bounding the event mass from a CW volume floor belongs in the endpoint client, not in
this finite structural module.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-! ## The finite 36-letter geometry -/

/-- A fine depth-one chunk letter is an ordered pair of supported base CW constituents. -/
abbrev CWDepthOneFineLetter := cwBlockSupport × cwBlockSupport

/-- The depth-one fine alphabet is inhabited, for example by the ordered pair `011 × 011`. -/
instance : Nonempty CWDepthOneFineLetter :=
  ⟨(⟨cw011, by decide⟩, ⟨cw011, by decide⟩)⟩

/-- The raw square address represented by a fine depth-one letter. -/
def cwDepthOneRawAddress (letter : CWDepthOneFineLetter) :
    BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1) :=
  cwSquareRawAddress letter.1.1 letter.2.1

/-- The coordinatewise total-weight shape of a fine depth-one letter. -/
def cwDepthOneCoarseShape (letter : CWDepthOneFineLetter) : CWSquareAddress :=
  coarsenBlockAddress cwSquareDegreeMap (cwDepthOneRawAddress letter)

/-- The ordered two-block word visible on one tensor leg. -/
def cwDepthOneLegWord (c : Leg) (letter : CWDepthOneFineLetter) :
    PositiveWord CWBlock 1 :=
  cwDepthOneRawAddress letter c

/-- Whether a base support address is one of the three one-dimensional corner constituents. -/
def cwBaseAddressIsCorner (address : cwBlockSupport) : Bool :=
  decide (address.1 = cw200 ∨ address.1 = cw020 ∨ address.1 = cw002)

/-- The exceptional event: at least one of the two base factors is a corner constituent. -/
def cwDepthOneHasCorner (letter : CWDepthOneFineLetter) : Bool :=
  cwBaseAddressIsCorner letter.1 || cwBaseAddressIsCorner letter.2

/-- Fine letters in one event class and one total-weight coarse fiber. -/
def cwDepthOneEventCoarseFiber (event : Bool) (shape : CWSquareAddress) :
    Finset CWDepthOneFineLetter :=
  Finset.univ.filter fun letter ↦
    cwDepthOneHasCorner letter = event ∧ cwDepthOneCoarseShape letter = shape

/-- The fine depth-one alphabet has exactly `6² = 36` letters. -/
@[simp] theorem card_cwDepthOneFineLetter : Fintype.card CWDepthOneFineLetter = 36 := by
  decide

/-- Inside every coarse shape, each of the no-corner and corner-containing classes has at most two
fine letters.

Proof sketch: enumerate the 36 ordered pairs and the 125 possible degree-sum shapes.  The familiar
coarse fiber sizes `1,2,3,4` split as `1+0`, `2+0`, `1+2`, or `2+2` between the two event classes.
-/
theorem card_cwDepthOneEventCoarseFiber_le_two
    (event : Bool) (shape : CWSquareAddress) :
    (cwDepthOneEventCoarseFiber event shape).card ≤ 2 := by
  set_option maxRecDepth 10000 in
    decide +revert

/-- A leg on which a no-corner letter of the supplied coarse shape has two middle blocks. -/
def cwDepthOneBlindLeg (shape : CWSquareAddress) : Leg :=
  if shape .X = 2 then .X else if shape .Y = 2 then .Y else .Z

/-- The constant two-middle word. -/
abbrev cwDepthOneMiddleWord : PositiveWord CWBlock 1 :=
  (.middle, .middle)

/-- On a fixed no-corner coarse fiber, the blind leg carries the constant two-middle word.

Proof sketch: a no-corner base address is one of `011`, `101`, `110`.  A coarse ordered-pair
shape always has a coordinate of degree two, and both letters are `middle` on that coordinate.
The finite proof checks all supported ordered pairs and shapes. -/
theorem cwDepthOneLegWord_blind_of_noCorner
    (shape : CWSquareAddress) (letter : CWDepthOneFineLetter)
    (hcommon : cwDepthOneHasCorner letter = false)
    (hshape : cwDepthOneCoarseShape letter = shape) :
    cwDepthOneLegWord (cwDepthOneBlindLeg shape) letter = cwDepthOneMiddleWord := by
  subst shape
  decide +revert

/-! ## Entropy of coarse conditional fibers -/

/-- A law supported in one event class has at most one bit of joint `(coarse, leg)` entropy after
conditioning on a fixed coarse shape.

Proof sketch: a positive conditional coordinate lies in the corresponding event/coarse fiber.
That fiber has at most two fine letters, so its deterministic joint observation has at most two
positive output coordinates.  A zero-mass coarse fiber uses the point-mass fallback and has zero
entropy. -/
private theorem entropyBits_conditionedPair_le_one
    (p : ProbabilityVector CWDepthOneFineLetter) (event : Bool)
    (hsupport : ∀ letter, 0 < p.weight letter → cwDepthOneHasCorner letter = event)
    (shape : CWSquareAddress) (c : Leg) :
    ((p.conditionOnFiber cwDepthOneCoarseShape shape).pushforward
      (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits ≤ 1 := by
  classical
  by_cases hmass : (p.pushforward cwDepthOneCoarseShape).weight shape = 0
  · rw [ProbabilityVector.conditionOnFiber_eq_pointMass_of_weight_eq_zero
        p cwDepthOneCoarseShape shape hmass,
      ProbabilityVector.pushforward_pointMass,
      ProbabilityVector.entropyBits_pointMass]
    norm_num
  · let conditioned := p.conditionOnFiber cwDepthOneCoarseShape shape
    apply ProbabilityVector.entropyBits_pushforward_le_one_of_support_card_le_two
      conditioned
      (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))
      (cwDepthOneEventCoarseFiber event shape)
    · intro letter hpositive
      have hfiber :=
        (ProbabilityVector.conditionOnFiber_weight_pos_iff_of_ne
          p cwDepthOneCoarseShape shape hmass letter).mp hpositive
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ letter, hsupport letter hfiber.2, hfiber.1⟩
    · exact card_cwDepthOneEventCoarseFiber_le_two event shape

/-- Every no-corner law has a leg with nonpositive double-coarse rate residual.

Proof sketch: choose a most likely coarse shape and its blind leg.  The conditional pair entropy
on that modal fiber is zero; every other coarse fiber contributes at most one bit.  Hence
`H₂(L_c | C) ≤ 1-p_max`.  The generic maximum-coordinate lower bound gives
`1-p_max ≤ H₂(C)`, proving `H₂(L_c | C)-H₂(C) ≤ 0`. -/
theorem exists_leg_entropyBits_pair_sub_two_mul_coarse_le_zero_of_noCorner
    (p : ProbabilityVector CWDepthOneFineLetter)
    (hsupport : ∀ letter, 0 < p.weight letter → cwDepthOneHasCorner letter = false) :
    ∃ c : Leg,
      (p.pushforward
          (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits -
        2 * (p.pushforward cwDepthOneCoarseShape).entropyBits ≤ 0 := by
  classical
  let coarseLaw := p.pushforward cwDepthOneCoarseShape
  obtain ⟨modal, _hmodalMem, hmodal⟩ :=
    Finset.exists_max_image (Finset.univ : Finset CWSquareAddress)
      coarseLaw.weight (by simp)
  let c := cwDepthOneBlindLeg modal
  refine ⟨c, ?_⟩
  have hcomponent : ∀ shape,
      ((p.conditionOnFiber cwDepthOneCoarseShape shape).pushforward
        (fun letter ↦
          (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits ≤
        if shape = modal then 0 else 1 := by
    intro shape
    by_cases hshape : shape = modal
    · subst shape
      simpa [c] using
        (ProbabilityVector.entropyBits_pushforward_pair_conditionOnFiber_eq_zero_of_constant
          p cwDepthOneCoarseShape (cwDepthOneLegWord c) modal cwDepthOneMiddleWord
          (fun letter hpositive hcoarse ↦ by
            simpa [c] using cwDepthOneLegWord_blind_of_noCorner modal letter
              (hsupport letter hpositive) hcoarse)).le
    · simpa [hshape] using entropyBits_conditionedPair_le_one p false hsupport shape c
  have hconditional :=
    ProbabilityVector.entropyBits_pair_sub_entropyBits_coarse_conditionOnFiber_le_sum
      p cwDepthOneCoarseShape (cwDepthOneLegWord c)
      (fun shape ↦ if shape = modal then 0 else 1) hcomponent
  have hsum :
      (∑ shape, coarseLaw.weight shape * (if shape = modal then 0 else 1)) =
        1 - coarseLaw.weight modal := by
    have hremove :
        (∑ shape, coarseLaw.weight shape * (if shape = modal then 0 else 1)) =
          ∑ shape ∈ (Finset.univ : Finset CWSquareAddress).erase modal,
            coarseLaw.weight shape := by
      calc
        (∑ shape, coarseLaw.weight shape * (if shape = modal then 0 else 1)) =
            coarseLaw.weight modal * (if modal = modal then 0 else 1) +
              ∑ shape ∈ (Finset.univ : Finset CWSquareAddress).erase modal,
                coarseLaw.weight shape * (if shape = modal then 0 else 1) :=
          (Finset.add_sum_erase (Finset.univ : Finset CWSquareAddress)
            (fun shape ↦ coarseLaw.weight shape * (if shape = modal then 0 else 1))
            (Finset.mem_univ modal)).symm
        _ = ∑ shape ∈ (Finset.univ : Finset CWSquareAddress).erase modal,
              coarseLaw.weight shape := by
          simp only [if_pos, mul_zero, zero_add]
          apply Finset.sum_congr rfl
          intro shape hshape
          have hne : shape ≠ modal := (Finset.mem_erase.mp hshape).1
          simp [hne]
    have htotal :
        coarseLaw.weight modal +
          ∑ shape ∈ (Finset.univ : Finset CWSquareAddress).erase modal,
            coarseLaw.weight shape = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ modal)]
      exact coarseLaw.total
    rw [hremove]
    linarith
  have hmax : ∀ shape, coarseLaw.weight shape ≤ coarseLaw.weight modal :=
    fun shape ↦ hmodal shape (Finset.mem_univ shape)
  have hlower :=
    ProbabilityVector.one_sub_weight_le_entropyBits_of_forall_weight_le
      coarseLaw modal hmax
  change
    (p.pushforward
        (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits -
      2 * coarseLaw.entropyBits ≤ 0
  change
    (p.pushforward
        (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits -
      coarseLaw.entropyBits ≤ _ at hconditional
  rw [hsum] at hconditional
  linarith

/-- Every corner-supported law has double-coarse rate residual at most one bit on every leg.

Proof sketch: after fixing the coarse shape there are at most two corner-containing fine letters,
so the conditional pair entropy is at most one bit.  Summing the coarse fibers gives
`H₂(L_c | C) ≤ 1`; subtracting the additional nonnegative `H₂(C)` proves the claim. -/
theorem entropyBits_pair_sub_two_mul_coarse_le_one_of_hasCorner
    (p : ProbabilityVector CWDepthOneFineLetter)
    (hsupport : ∀ letter, 0 < p.weight letter → cwDepthOneHasCorner letter = true)
    (c : Leg) :
    (p.pushforward
        (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits -
      2 * (p.pushforward cwDepthOneCoarseShape).entropyBits ≤ 1 := by
  have hcomponent : ∀ shape,
      ((p.conditionOnFiber cwDepthOneCoarseShape shape).pushforward
        (fun letter ↦
          (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits ≤ 1 :=
    fun shape ↦ entropyBits_conditionedPair_le_one p true hsupport shape c
  have hconditional :=
    ProbabilityVector.entropyBits_pair_sub_entropyBits_coarse_conditionOnFiber_le_sum
      p cwDepthOneCoarseShape (cwDepthOneLegWord c) (fun _shape ↦ 1) hcomponent
  have hcoarseNonneg :
      0 ≤ (p.pushforward cwDepthOneCoarseShape).entropyBits := by
    unfold ProbabilityVector.entropyBits
    exact div_nonneg (p.pushforward cwDepthOneCoarseShape).entropy_nonneg
      (Real.log_pos (by norm_num)).le
  have hsum :
      (∑ shape, (p.pushforward cwDepthOneCoarseShape).weight shape * (1 : ℝ)) = 1 := by
    simpa using (p.pushforward cwDepthOneCoarseShape).total
  rw [hsum] at hconditional
  linarith

/-! ## The event-split structural barrier -/

/-- For every law on the 36 depth-one letters, one leg's global-competitor residual is bounded by
the entropy of the corner event plus its probability.

Proof sketch: condition on `cwDepthOneHasCorner`.  If the common component has positive mass, use
the modal-blind-leg theorem; otherwise it is the point-mass fallback and any leg works.  The
exceptional component has the uniform one-bit bound on that same leg.  The double-coarse mixture
theorem then charges exactly `H₂(B) + P(B=true)`. -/
theorem exists_leg_depthOne_rateResidual_le_cornerEntropy_add_mass
    (p : ProbabilityVector CWDepthOneFineLetter) :
    ∃ c : Leg,
      (p.pushforward
          (fun letter ↦ (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits -
        2 * (p.pushforward cwDepthOneCoarseShape).entropyBits ≤
      (p.pushforward cwDepthOneHasCorner).entropyBits +
        (p.pushforward cwDepthOneHasCorner).weight true := by
  classical
  let common := p.conditionOnFiber cwDepthOneHasCorner false
  let exceptional := p.conditionOnFiber cwDepthOneHasCorner true
  have hexceptionalBound (c : Leg) :
      (exceptional.pushforward
          (fun letter ↦
            (cwDepthOneCoarseShape letter, cwDepthOneLegWord c letter))).entropyBits -
        2 * (exceptional.pushforward cwDepthOneCoarseShape).entropyBits ≤ 1 := by
    by_cases hmass : (p.pushforward cwDepthOneHasCorner).weight true = 0
    · rw [show exceptional =
          ProbabilityVector.pointMass
            (Classical.choice (inferInstance : Nonempty CWDepthOneFineLetter)) by
          exact ProbabilityVector.conditionOnFiber_eq_pointMass_of_weight_eq_zero
            p cwDepthOneHasCorner true hmass]
      simp
    · apply entropyBits_pair_sub_two_mul_coarse_le_one_of_hasCorner exceptional
      intro letter hpositive
      exact
          (ProbabilityVector.conditionOnFiber_weight_pos_iff_of_ne
            p cwDepthOneHasCorner true hmass letter).mp hpositive |>.1
  by_cases hcommonMass : (p.pushforward cwDepthOneHasCorner).weight false = 0
  · refine ⟨.X, ?_⟩
    have hcommon :
        (common.pushforward
            (fun letter ↦
              (cwDepthOneCoarseShape letter, cwDepthOneLegWord .X letter))).entropyBits -
          2 * (common.pushforward cwDepthOneCoarseShape).entropyBits ≤ 0 := by
      rw [show common =
          ProbabilityVector.pointMass
            (Classical.choice (inferInstance : Nonempty CWDepthOneFineLetter)) by
          exact ProbabilityVector.conditionOnFiber_eq_pointMass_of_weight_eq_zero
            p cwDepthOneHasCorner false hcommonMass]
      simp
    exact ProbabilityVector.entropyBits_pair_sub_two_mul_entropyBits_coarse_boolConditioning_le
      p cwDepthOneHasCorner cwDepthOneCoarseShape (cwDepthOneLegWord .X)
      hcommon (hexceptionalBound .X)
  · have hcommonSupport : ∀ letter, 0 < common.weight letter →
        cwDepthOneHasCorner letter = false := by
      intro letter hpositive
      exact
        (ProbabilityVector.conditionOnFiber_weight_pos_iff_of_ne
          p cwDepthOneHasCorner false hcommonMass letter).mp hpositive |>.1
    obtain ⟨c, hcommon⟩ :=
      exists_leg_entropyBits_pair_sub_two_mul_coarse_le_zero_of_noCorner
        common hcommonSupport
    refine ⟨c, ?_⟩
    exact ProbabilityVector.entropyBits_pair_sub_two_mul_entropyBits_coarse_boolConditioning_le
      p cwDepthOneHasCorner cwDepthOneCoarseShape (cwDepthOneLegWord c)
      hcommon (hexceptionalBound c)

end AlgebraicComplexity.Examples
