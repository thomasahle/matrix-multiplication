/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotient

/-!
# Tight quotients of the depth-one Coppersmith--Winograd support

This file starts from the physical support of two independently chosen CW constituents.  A raw
split address is obtained by transposing the two supported constituent addresses and then applying
the native complete-split encoding on each leg.  Thus `cwRawSplitSupport` is the actual chunk
support, not a synthetic coordinatewise superset.

The main result below characterizes every surjective legwise quotient of the depth-one support
whose image is tight.  Its proof is an explicit additive decoder.  Rectangle relations separate
the two digit positions, and the six base-CW relations force one common slope on all three legs.
No finite support is exhaustively evaluated.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-- Transpose a word of supported base CW addresses and encode each leg as a complete-split
word. -/
def cwRawSplitAddress (depth : ℕ)
    (source : PositiveWord cwBlockSupport (2 ^ depth - 1)) :
    BlockAddress (fun _c ↦ SplitWord depth) :=
  fun c ↦ cwChunkSplitWord depth
    (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) source c)

/-- The physical complete-split support of a chunk containing `2^depth` base CW factors. -/
noncomputable def cwRawSplitSupport (depth : ℕ) :
    Finset (BlockAddress (fun _c ↦ SplitWord depth)) := by
  classical
  exact Finset.univ.image (cwRawSplitAddress depth)

/-- Complete-split encoding loses no supported source word. -/
theorem cwRawSplitAddress_injective (depth : ℕ) :
    Function.Injective (cwRawSplitAddress depth) := by
  intro left right haddress
  have htranspose :
      positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) left =
        positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) right := by
    funext c
    apply cwChunkSplitWord_injective depth
    exact congrFun haddress c
  rw [positiveSupportWordBlockAddress_eq_equiv_map,
    positiveSupportWordBlockAddress_eq_equiv_map] at htranspose
  have hword :=
    (positiveWordBlockAddressEquiv (fun _c : Leg ↦ CWBlock) (2 ^ depth - 1)).injective
      htranspose
  exact positiveWordMap_injective Subtype.val_injective (2 ^ depth - 1) hword

/-- The structural raw support has one element for every word of supported base addresses. -/
theorem card_cwRawSplitSupport (depth : ℕ) :
    (cwRawSplitSupport depth).card = cwBlockSupport.card ^ (2 ^ depth) := by
  classical
  rw [cwRawSplitSupport,
    Finset.card_image_of_injective _ (cwRawSplitAddress_injective depth),
    Finset.card_univ]
  calc
    Fintype.card (PositiveWord cwBlockSupport (2 ^ depth - 1)) =
        Fintype.card (Fin (2 ^ depth - 1 + 1) → cwBlockSupport) :=
      Fintype.card_congr (positiveWordEquiv cwBlockSupport (2 ^ depth - 1))
    _ = Fintype.card cwBlockSupport ^ (2 ^ depth - 1 + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    _ = cwBlockSupport.card ^ (2 ^ depth) := by
      rw [Fintype.card_coe, two_pow_sub_one_add_one]

/-- Applying the native complete-split encoding to the chunk support gives exactly the structural
raw support. -/
theorem cwChunkPartitionedTensor_support_image_splitWord
    (K : Type u) [CommRing K] (q depth : ℕ) :
    (cwChunkPartitionedTensor K q depth).support.image
        (coarsenBlockAddress (fun _c ↦ cwChunkSplitWord depth)) =
      cwRawSplitSupport depth := by
  classical
  unfold cwChunkPartitionedTensor
  rw [PartitionedTensor.positivePower_support_eq_image_positiveSupportWordBlockAddress]
  unfold cwRawSplitSupport
  rw [Finset.image_image]
  apply Finset.image_congr
  intro source _hsource
  rfl

/-- Every raw supported split address satisfies the base CW equation at every digit position. -/
theorem cwRawSplitSupport_digit_sum
    (depth : ℕ) (address : BlockAddress (fun _c ↦ SplitWord depth))
    (haddress : address ∈ cwRawSplitSupport depth) (position : Fin (2 ^ depth)) :
    ∑ c, (address c position : ℕ) = 2 := by
  classical
  rw [cwRawSplitSupport, Finset.mem_image] at haddress
  obtain ⟨source, _hsource, rfl⟩ := haddress
  let sample : Fin (2 ^ depth - 1 + 1) := (cwChunkPositionEquiv depth).symm position
  let atom := positiveWordEquiv cwBlockSupport (2 ^ depth - 1) source sample
  have hatom : atom.1 ∈ cwBlockSupport := atom.2
  have hsum := cwBlockSupport_digit_sum atom.1 hatom
  have hread (c : Leg) :
      positiveWordEquiv CWBlock (2 ^ depth - 1)
          (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) source c)
          sample = atom.1 c := by
    exact congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress
        cwBlockSupport (2 ^ depth - 1) source c) sample
  change
    ∑ c, (cwBlockDigit
      (positiveWordEquiv CWBlock (2 ^ depth - 1)
        (positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) source c)
        sample) : ℕ) = 2
  simp_rw [hread]
  exact hsum

/-- Summing the complete-split weights of all three legs gives the full legal coarse total. -/
theorem cwRawSplitSupport_weight_sum
    (depth : ℕ) (address : BlockAddress (fun _c ↦ SplitWord depth))
    (haddress : address ∈ cwRawSplitSupport depth) :
    ∑ c, splitWordWeight (address c) = coarseTotal depth := by
  classical
  unfold splitWordWeight
  rw [Finset.sum_comm]
  calc
    (∑ position : Fin (2 ^ depth), ∑ c, (address c position : ℕ)) =
        ∑ _position : Fin (2 ^ depth), 2 := by
      apply Finset.sum_congr rfl
      intro position _hposition
      exact cwRawSplitSupport_digit_sum depth address haddress position
    _ = coarseTotal depth := by
      simp [coarseTotal, pow_succ, Nat.mul_comm]

/-- The raw support at depth one: two independently supported base CW addresses. -/
noncomputable abbrev cwDepthOneRawSupport :
    Finset (BlockAddress (fun _c ↦ SplitWord 1)) :=
  cwRawSplitSupport 1

/-- Image of the physical depth-one support under an arbitrary legwise quotient. -/
noncomputable def cwDepthOneQuotientSupport
    {Q : Leg → Type*} [∀ c, Fintype (Q c)] [∀ c, DecidableEq (Q c)]
    (quotient : ∀ c, SplitWord 1 → Q c) : Finset (BlockAddress Q) := by
  classical
  exact cwDepthOneRawSupport.image (coarsenBlockAddress quotient)

/-- Total-weight image of the physical complete-split support. -/
noncomputable def cwTotalWeightSplitSupport (depth : ℕ) :
    Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth)) := by
  classical
  exact (cwRawSplitSupport depth).image
    (coarsenBlockAddress (cwSplitWordTotalCoarsening depth))

/-- The total-weight quotient remains tight at every chunk depth.  Its injective integer label is
the visible value of the finite total digit. -/
theorem cwTotalWeightSplitSupport_isTight (depth : ℕ) :
    IsTightSupport (cwTotalWeightSplitSupport depth) := by
  classical
  refine ⟨fun _c digit ↦ (digit.val : ℤ), ?_, (coarseTotal depth : ℤ), ?_⟩
  · intro c left right heq
    apply Fin.ext
    exact Int.ofNat_inj.mp heq
  · intro address haddress
    rw [cwTotalWeightSplitSupport, Finset.mem_image] at haddress
    obtain ⟨fine, hfine, rfl⟩ := haddress
    simp only [coarsenBlockAddress_apply, cwSplitWordTotalCoarsening,
      cwSplitWordTotalDigit_val]
    exact_mod_cast cwRawSplitSupport_weight_sum depth fine hfine

/-! ## Additive decoding at depth one -/

/-- The CW block carrying a prescribed ternary split digit in the tight-quotient decoder. -/
def cwTightBlockOfSplitDigit (digit : SplitDigit) : CWBlock :=
  ![CWBlock.zero, CWBlock.middle, CWBlock.last] digit

@[simp] theorem cwBlockDigit_cwTightBlockOfSplitDigit (digit : SplitDigit) :
    cwBlockDigit (cwTightBlockOfSplitDigit digit) = digit := by
  fin_cases digit <;> rfl

/-- A supported base address whose digit on `c` is prescribed and whose next leg is zero. -/
def cwTightRowAddress : (c : Leg) → SplitDigit → CWBlockAddress
  | .X, digit => cwBlockAddress
      (cwTightBlockOfSplitDigit digit) .zero (cwTightBlockOfSplitDigit (Fin.rev digit))
  | .Y, digit => cwBlockAddress
      (cwTightBlockOfSplitDigit (Fin.rev digit)) (cwTightBlockOfSplitDigit digit) .zero
  | .Z, digit => cwBlockAddress
      .zero (cwTightBlockOfSplitDigit (Fin.rev digit)) (cwTightBlockOfSplitDigit digit)

/-- A supported base address whose digit on `c` is prescribed and whose previous leg is zero. -/
def cwTightColumnAddress : (c : Leg) → SplitDigit → CWBlockAddress
  | .X, digit => cwBlockAddress
      (cwTightBlockOfSplitDigit digit) (cwTightBlockOfSplitDigit (Fin.rev digit)) .zero
  | .Y, digit => cwBlockAddress
      .zero (cwTightBlockOfSplitDigit digit) (cwTightBlockOfSplitDigit (Fin.rev digit))
  | .Z, digit => cwBlockAddress
      (cwTightBlockOfSplitDigit (Fin.rev digit)) .zero (cwTightBlockOfSplitDigit digit)

private theorem cwTightRowAddress_mem (c : Leg) (digit : SplitDigit) :
    cwTightRowAddress c digit ∈ cwBlockSupport := by
  cases c <;> fin_cases digit <;>
    simp [cwTightRowAddress, cwTightBlockOfSplitDigit, cwBlockSupport, cwBlockAddress,
      cw200, cw020, cw002, cw011, cw101, cw110]

private theorem cwTightColumnAddress_mem (c : Leg) (digit : SplitDigit) :
    cwTightColumnAddress c digit ∈ cwBlockSupport := by
  cases c <;> fin_cases digit <;>
    simp [cwTightColumnAddress, cwTightBlockOfSplitDigit, cwBlockSupport, cwBlockAddress,
      cw200, cw020, cw002, cw011, cw101, cw110]

/-- The supported row address, packaged with its support proof. -/
private def cwTightRowSupported (c : Leg) (digit : SplitDigit) : cwBlockSupport :=
  ⟨cwTightRowAddress c digit, cwTightRowAddress_mem c digit⟩

/-- The supported column address, packaged with its support proof. -/
private def cwTightColumnSupported (c : Leg) (digit : SplitDigit) : cwBlockSupport :=
  ⟨cwTightColumnAddress c digit, cwTightColumnAddress_mem c digit⟩

/-- A raw length-two source made from two independently supported base addresses. -/
private def cwRawPairSource (left right : cwBlockSupport) :
    PositiveWord cwBlockSupport 1 :=
  (left, right)

@[simp] private theorem cwRawSplitAddress_cwRawPairSource
    (left right : cwBlockSupport) (c : Leg) :
    cwRawSplitAddress 1 (cwRawPairSource left right) c =
      cwSplitPair (cwBlockDigit (left.1 c)) (cwBlockDigit (right.1 c)) := by
  funext position
  fin_cases position <;> rfl

private theorem cwRawSplitAddress_cwRawPairSource_mem
    (left right : cwBlockSupport) :
    cwRawSplitAddress 1 (cwRawPairSource left right) ∈ cwDepthOneRawSupport := by
  change cwRawSplitAddress 1 (cwRawPairSource left right) ∈ cwRawSplitSupport 1
  rw [cwRawSplitSupport]
  exact Finset.mem_image.mpr ⟨cwRawPairSource left right, Finset.mem_univ _, rfl⟩

/-- The integer linear form on a two-digit split word used by every tight quotient. -/
def cwSplitLinearForm (lambda mu : ℤ) (word : SplitWord 1) : ℤ :=
  lambda * (word 0 : ℤ) + mu * (word 1 : ℤ)

@[simp] theorem cwSplitPair_eta (word : SplitWord 1) :
    cwSplitPair (word 0) (word 1) = word := by
  funext position
  fin_cases position <;> rfl

/-- Rectangle relations in the product CW support isolate any chosen leg. -/
private theorem cwPairWeight_rectangle
    (g : ∀ _c : Leg, SplitWord 1 → ℤ) (D : ℤ)
    (hconstant : ∀ left right : cwBlockSupport,
      ∑ c, g c (cwSplitPair (cwBlockDigit (left.1 c))
        (cwBlockDigit (right.1 c))) = D)
    (c : Leg) (a a' b b' : SplitDigit) :
    g c (cwSplitPair a b) + g c (cwSplitPair a' b') =
      g c (cwSplitPair a b') + g c (cwSplitPair a' b) := by
  have h00 := hconstant (cwTightRowSupported c a) (cwTightColumnSupported c b)
  have h11 := hconstant (cwTightRowSupported c a') (cwTightColumnSupported c b')
  have h01 := hconstant (cwTightRowSupported c a) (cwTightColumnSupported c b')
  have h10 := hconstant (cwTightRowSupported c a') (cwTightColumnSupported c b)
  cases c <;>
    simp only [sum_leg, cwTightRowSupported, cwTightColumnSupported,
      cwTightRowAddress, cwTightColumnAddress, cwBlockAddress,
      ofLegs_X, ofLegs_Y, ofLegs_Z, cwBlockDigit_cwTightBlockOfSplitDigit,
      cwBlockDigit_zero] at h00 h11 h01 h10 ⊢ <;>
    linear_combination h00 + h11 - h01 - h10

/-- The six CW relations force every legal one-position weighting to have one common slope on all
three legs. -/
private theorem cwBaseWeight_affine
    (f : ∀ _c : Leg, SplitDigit → ℤ) (D : ℤ)
    (hconstant : ∀ address ∈ cwBlockSupport,
      ∑ c, f c (cwBlockDigit (address c)) = D) :
    ∃ slope : ℤ, ∀ c digit,
      f c digit = f c 0 + slope * (digit : ℤ) := by
  have h200 : f .X 2 + f .Y 0 + f .Z 0 = D := by
    simpa [cw200, cwBlockAddress, cwBlockDigit, sum_leg] using
      hconstant cw200 (by simp [cwBlockSupport])
  have h020 : f .X 0 + f .Y 2 + f .Z 0 = D := by
    simpa [cw020, cwBlockAddress, cwBlockDigit, sum_leg] using
      hconstant cw020 (by simp [cwBlockSupport])
  have h002 : f .X 0 + f .Y 0 + f .Z 2 = D := by
    simpa [cw002, cwBlockAddress, cwBlockDigit, sum_leg] using
      hconstant cw002 (by simp [cwBlockSupport])
  have h011 : f .X 0 + f .Y 1 + f .Z 1 = D := by
    simpa [cw011, cwBlockAddress, cwBlockDigit, sum_leg] using
      hconstant cw011 (by simp [cwBlockSupport])
  have h101 : f .X 1 + f .Y 0 + f .Z 1 = D := by
    simpa [cw101, cwBlockAddress, cwBlockDigit, sum_leg] using
      hconstant cw101 (by simp [cwBlockSupport])
  have h110 : f .X 1 + f .Y 1 + f .Z 0 = D := by
    simpa [cw110, cwBlockAddress, cwBlockDigit, sum_leg] using
      hconstant cw110 (by simp [cwBlockSupport])
  let slope := f .X 1 - f .X 0
  have hY1 : f .Y 1 - f .Y 0 = slope := by
    dsimp only [slope]
    linear_combination h011 - h101
  have hZ1 : f .Z 1 - f .Z 0 = slope := by
    dsimp only [slope]
    linear_combination h011 - h110
  have hX2 : f .X 2 - f .X 1 = slope := by
    linear_combination h200 - h110 + hY1
  have hY2 : f .Y 2 - f .Y 1 = slope := by
    dsimp only [slope]
    linear_combination h020 - h110
  have hZ2 : f .Z 2 - f .Z 1 = slope := by
    dsimp only [slope]
    linear_combination h002 - h101
  refine ⟨slope, ?_⟩
  intro c digit
  cases c <;> fin_cases digit <;> simp [slope] <;> omega

/-- A surjective legwise quotient of the physical depth-one CW support is tight exactly when its
fibers are the fibers of one integer linear form, with the same two slopes on all three legs. -/
theorem cwDepthOneQuotientSupport_isTight_iff_fibers_linear
    {Q : Leg → Type*} [∀ c, Fintype (Q c)] [∀ c, DecidableEq (Q c)]
    (quotient : ∀ c, SplitWord 1 → Q c)
    (hsurjective : ∀ c, Function.Surjective (quotient c)) :
    IsTightSupport (cwDepthOneQuotientSupport quotient) ↔
      ∃ lambda mu : ℤ, ∀ c left right,
        quotient c left = quotient c right ↔
          cwSplitLinearForm lambda mu left = cwSplitLinearForm lambda mu right := by
  classical
  constructor
  · rintro ⟨weight, hweight, D, hconstant⟩
    let g : ∀ _c : Leg, SplitWord 1 → ℤ :=
      fun c word ↦ weight c (quotient c word)
    have hpair : ∀ left right : cwBlockSupport,
        ∑ c, g c (cwSplitPair (cwBlockDigit (left.1 c))
          (cwBlockDigit (right.1 c))) = D := by
      intro left right
      have hraw := cwRawSplitAddress_cwRawPairSource_mem left right
      have himage :
          coarsenBlockAddress quotient
              (cwRawSplitAddress 1 (cwRawPairSource left right)) ∈
            cwDepthOneQuotientSupport quotient := by
        rw [cwDepthOneQuotientSupport]
        exact Finset.mem_image.mpr ⟨_, hraw, rfl⟩
      simpa only [g, coarsenBlockAddress_apply,
        cwRawSplitAddress_cwRawPairSource] using hconstant _ himage
    let first : ∀ _c : Leg, SplitDigit → ℤ := fun c digit ↦
      g c (cwSplitPair digit 0) - g c (cwSplitPair 0 0)
    let second : ∀ _c : Leg, SplitDigit → ℤ := fun c digit ↦
      g c (cwSplitPair 0 digit)
    have hseparate (c : Leg) (a b : SplitDigit) :
        g c (cwSplitPair a b) = first c a + second c b := by
      have hrectangle := cwPairWeight_rectangle g D hpair c a 0 b 0
      dsimp only [first, second]
      linear_combination hrectangle
    let anchor : cwBlockSupport := ⟨cw200, by simp [cwBlockSupport]⟩
    let firstTarget := D - ∑ c, second c (cwBlockDigit (anchor.1 c))
    have hfirstConstant : ∀ address ∈ cwBlockSupport,
        ∑ c, first c (cwBlockDigit (address c)) = firstTarget := by
      intro address haddress
      have h := hpair ⟨address, haddress⟩ anchor
      simp_rw [hseparate] at h
      rw [Finset.sum_add_distrib] at h
      dsimp only [firstTarget]
      linear_combination h
    let secondTarget := D - ∑ c, first c (cwBlockDigit (anchor.1 c))
    have hsecondConstant : ∀ address ∈ cwBlockSupport,
        ∑ c, second c (cwBlockDigit (address c)) = secondTarget := by
      intro address haddress
      have h := hpair anchor ⟨address, haddress⟩
      simp_rw [hseparate] at h
      rw [Finset.sum_add_distrib] at h
      dsimp only [secondTarget]
      linear_combination h
    obtain ⟨lambda, hfirstAffine⟩ :=
      cwBaseWeight_affine first firstTarget hfirstConstant
    obtain ⟨mu, hsecondAffine⟩ :=
      cwBaseWeight_affine second secondTarget hsecondConstant
    have hgform (c : Leg) (word : SplitWord 1) :
        g c word = first c 0 + second c 0 + cwSplitLinearForm lambda mu word := by
      calc
        g c word = first c (word 0) + second c (word 1) :=
          by simpa only [cwSplitPair_eta] using hseparate c (word 0) (word 1)
        _ = (first c 0 + lambda * (word 0 : ℤ)) +
            (second c 0 + mu * (word 1 : ℤ)) := by
          rw [hfirstAffine c (word 0), hsecondAffine c (word 1)]
        _ = first c 0 + second c 0 + cwSplitLinearForm lambda mu word := by
          simp only [cwSplitLinearForm]
          ring
    refine ⟨lambda, mu, ?_⟩
    intro c left right
    constructor
    · intro hquotient
      have hg : g c left = g c right := by
        dsimp only [g]
        rw [hquotient]
      rw [hgform c left, hgform c right] at hg
      linear_combination hg
    · intro hlinear
      apply hweight c
      change g c left = g c right
      rw [hgform c left, hgform c right, hlinear]
  · rintro ⟨lambda, mu, hfibers⟩
    let representative : ∀ c, Q c → SplitWord 1 :=
      fun c ↦ Function.surjInv (hsurjective c)
    have hrepresentative (c : Leg) (label : Q c) :
        quotient c (representative c label) = label := by
      dsimp only [representative]
      exact Function.surjInv_eq (hsurjective c) label
    let quotientWeight : ∀ c, Q c → ℤ := fun c label ↦
      cwSplitLinearForm lambda mu (representative c label)
    have hquotientWeight_injective (c : Leg) :
        Function.Injective (quotientWeight c) := by
      intro left right heq
      have hlinear :
          cwSplitLinearForm lambda mu (representative c left) =
            cwSplitLinearForm lambda mu (representative c right) := by
        exact heq
      have hquotient :=
        (hfibers c (representative c left) (representative c right)).mpr hlinear
      rw [hrepresentative c left, hrepresentative c right] at hquotient
      exact hquotient
    have hquotientWeight_quotient (c : Leg) (word : SplitWord 1) :
        quotientWeight c (quotient c word) = cwSplitLinearForm lambda mu word := by
      dsimp only [quotientWeight]
      apply (hfibers c (representative c (quotient c word)) word).mp
      exact hrepresentative c (quotient c word)
    refine ⟨quotientWeight, hquotientWeight_injective,
      2 * lambda + 2 * mu, ?_⟩
    intro address haddress
    rw [cwDepthOneQuotientSupport, Finset.mem_image] at haddress
    obtain ⟨fine, hfine, rfl⟩ := haddress
    simp_rw [coarsenBlockAddress_apply, hquotientWeight_quotient]
    have hzero : ∑ c, (fine c 0 : ℤ) = 2 := by
      exact_mod_cast cwRawSplitSupport_digit_sum 1 fine hfine 0
    have hone : ∑ c, (fine c 1 : ℤ) = 2 := by
      exact_mod_cast cwRawSplitSupport_digit_sum 1 fine hfine 1
    calc
      (∑ c, cwSplitLinearForm lambda mu (fine c)) =
          lambda * (∑ c, (fine c 0 : ℤ)) +
            mu * (∑ c, (fine c 1 : ℤ)) := by
        simp only [cwSplitLinearForm, Finset.sum_add_distrib]
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = 2 * lambda + 2 * mu := by
        rw [hzero, hone]
        ring

end AlgebraicComplexity.Examples
